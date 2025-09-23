import math
import subprocess
import os
from typing import List, Dict


class CompleteSMT2Analyzer:
    """
    完整的SMT2关系分析器，使用数值编码代替字符串
    """

    def __init__(self, temp_dir: str = "./temp_smt"):
        self.temp_dir = temp_dir
        os.makedirs(temp_dir, exist_ok=True)
        self.dreal_path = "/opt/dreal/4.21.06.2/bin/dreal"

        # 关系类型编码
        self.RELATION_CODES = {
            "none": 0,
            "ahead": 1,
            "behind": 2,
            "left": 3,
            "right": 4,
            "toward": 5,
            "away": 6
        }

        self.CODE_TO_RELATION = {v: k for k, v in self.RELATION_CODES.items()}

    def generate_complete_smt2(self,points: List[Dict]) -> str:
        smt_code = f"""(set-logic QF_NRA)

    ; ==================== 辅助函数定义 ====================
    (define-fun normalize_angle ((angle Real)) Real
        (ite (> angle 360.0) (- angle 360.0)
        (ite (< angle 0.0) (+ angle 360.0)
        angle)))

    (define-fun relative_angle_diff ((a Real) (b Real)) Real
        (let ((diff_raw (- (normalize_angle a) (normalize_angle b))))
            (normalize_angle diff_raw)))

    (define-fun relative_bearing ((Ax Real) (Ay Real) (Bx Real) (By Real)) Real
        (let ((dx (- Bx Ax))
              (dy (- By Ay)))
            (let ((angle_rad (atan2 dy dx)))
                (let ((angle_deg_normal (* (- angle_rad (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))
                    (normalize_angle angle_deg_normal)))))

    ; 空间关系判断函数
    (define-fun is_ahead ((ref_heading Real) (bearing Real)) Bool
        (let ((diff (relative_angle_diff bearing ref_heading)))
            (or (and (>= diff 0.0) (<= diff 10.0))
                (and (>= diff 350.0) (<= diff 360.0)))))

    (define-fun is_behind ((ref_heading Real) (bearing Real)) Bool
        (let ((diff (relative_angle_diff bearing ref_heading)))
            (and (>= diff 170.0) (<= diff 190.0))))

    (define-fun is_left ((ref_heading Real) (bearing Real)) Bool
        (let ((diff (relative_angle_diff bearing ref_heading)))
            (and (>= diff 80.0) (<= diff 100.0))))

    (define-fun is_right ((ref_heading Real) (bearing Real)) Bool
        (let ((diff (relative_angle_diff bearing ref_heading)))
            (and (>= diff 260.0) (<= diff 280.0))))

    ; 朝向关系判断函数
    (define-fun is_toward ((ref_x Real) (ref_y Real) (point_x Real) (point_y Real) (point_heading Real)) Bool
        (let ((bearing (relative_bearing point_x point_y ref_x ref_y)))
            (<= (relative_angle_diff bearing point_heading) 10.0)))

    (define-fun is_away ((ref_x Real) (ref_y Real) (point_x Real) (point_y Real) (point_heading Real)) Bool
        (let ((bearing (relative_bearing ref_x ref_y point_x point_y)))
            (<= (relative_angle_diff bearing point_heading) 10.0)))

    ; ==================== 变量声明 ====================
    """

        # 声明所有点的坐标和朝向变量
        for point in points:
            smt_code += f"(declare-const {point['id']}_x Real)\n"
            smt_code += f"(declare-const {point['id']}_y Real)\n"
            smt_code += f"(declare-const {point['id']}_heading Real)\n"

        # 声明关系变量
        for i in range(1, len(points)):
            current_point = points[i]
            for j in range(i):
                ref_point = points[j]
                smt_code += f"(declare-const spatial_{current_point['id']}_{ref_point['id']} Real)\n"
                smt_code += f"(declare-const orient_{current_point['id']}_{ref_point['id']} Real)\n"

        smt_code += "\n; ==================== 已知值约束 ====================\n"

        # 设置所有点的已知值
        for point in points:
            smt_code += f"(assert (= {point['id']}_x {point['x']}))\n"
            smt_code += f"(assert (= {point['id']}_y {point['y']}))\n"
            smt_code += f"(assert (= {point['id']}_heading {point['heading']}))\n"

        # 设置关系变量的范围约束
        for i in range(1, len(points)):
            current_point = points[i]
            for j in range(i):
                ref_point = points[j]
                smt_code += f"(assert (>= spatial_{current_point['id']}_{ref_point['id']} 0.0))\n"
                smt_code += f"(assert (<= spatial_{current_point['id']}_{ref_point['id']} 4.0))\n"
                smt_code += f"(assert (>= orient_{current_point['id']}_{ref_point['id']} 0.0))\n"
                smt_code += f"(assert (<= orient_{current_point['id']}_{ref_point['id']} 6.0))\n"

        smt_code += "\n; ==================== 关系约束 ====================\n"

        # 为每个点对添加关系约束
        for i in range(1, len(points)):
            current_point = points[i]
            for j in range(i):
                ref_point = points[j]

                # 使用 define-fun 定义方位角（关键修复！）
                bearing_var = f"bearing_{current_point['id']}_{ref_point['id']}"
                smt_code += f"""
    ; 计算 {current_point['id']} 相对于 {ref_point['id']} 的方位角
    (define-fun {bearing_var} () Real
        (relative_bearing {ref_point['id']}_x {ref_point['id']}_y {current_point['id']}_x {current_point['id']}_y))
    """

                # 空间关系约束
                smt_code += f"""
    ; {current_point['id']} 与 {ref_point['id']} 的空间关系
    (assert (or
        (and (is_ahead {ref_point['id']}_heading {bearing_var}) (= spatial_{current_point['id']}_{ref_point['id']} 0.0))
        (and (is_ahead {ref_point['id']}_heading {bearing_var}) (= spatial_{current_point['id']}_{ref_point['id']} 1.0))
        (and (is_behind {ref_point['id']}_heading {bearing_var}) (= spatial_{current_point['id']}_{ref_point['id']} 2.0))
        (and (is_left {ref_point['id']}_heading {bearing_var}) (= spatial_{current_point['id']}_{ref_point['id']} 3.0))
        (and (is_right {ref_point['id']}_heading {bearing_var}) (= spatial_{current_point['id']}_{ref_point['id']} 4.0))
    ))
    """

                # 朝向关系约束
                smt_code += f"""
    ; {current_point['id']} 与 {ref_point['id']} 的朝向关系
    (assert (or
        (and (is_toward {ref_point['id']}_x {ref_point['id']}_y {current_point['id']}_x {current_point['id']}_y {current_point['id']}_heading)
             (= orient_{current_point['id']}_{ref_point['id']} 5.0))
        (and (is_away {ref_point['id']}_x {ref_point['id']}_y {current_point['id']}_x {current_point['id']}_y {current_point['id']}_heading)
             (= orient_{current_point['id']}_{ref_point['id']} 6.0))
        (= orient_{current_point['id']}_{ref_point['id']} 0.0)
    ))
    """

        smt_code += "\n; ==================== 求解 ====================\n"
        smt_code += "(check-sat)\n"
        smt_code += "(get-value ("

        # 添加所有需要获取值的变量
        value_vars = []
        for i in range(1, len(points)):
            current_point = points[i]
            for j in range(i):
                ref_point = points[j]
                value_vars.append(f"spatial_{current_point['id']}_{ref_point['id']}")
                value_vars.append(f"orient_{current_point['id']}_{ref_point['id']}")

        smt_code += " ".join(value_vars)
        smt_code += "))\n"

        return smt_code




    def write_smt_file(self, smt_code: str, filename: str = "complete_relations.smt2") -> str:
        """写入SMT2文件"""
        file_path = os.path.join(self.temp_dir, filename)
        with open(file_path, "w") as f:
            f.write(smt_code)
        return file_path

    def run_smt_solver(self, file_path: str) -> tuple:
        """运行SMT求解器"""
        try:
            result = subprocess.run(
                [self.dreal_path, file_path],
                capture_output=True,
                text=True,
                timeout=30
            )

            output = result.stdout.strip()
            error_output = result.stderr.strip()

            if "sat" in output.lower():
                return (True, "sat", output)
            elif "unsat" in output.lower():
                return (True, "unsat", output)
            elif "delta-sat" in output.lower():
                return (True, "delta-sat", output)

            if error_output:
                return (False, "error", error_output)

            return (False, "unknown", output)

        except subprocess.TimeoutExpired:
            return (False, "timeout", "Solver timeout")
        except Exception as e:
            return (False, "exception", str(e))

    def parse_model_output(self, output: str) -> Dict:
        """解析求解器输出"""
        results = {}
        lines = output.split('\n')

        for line in lines:
            line = line.strip()
            if line.startswith('((') and line.endswith('))'):
                content = line[2:-2]
                pairs = content.split(') (')
                for pair in pairs:
                    pair = pair.replace('(', '').replace(')', '').strip()
                    parts = pair.split()
                    if len(parts) >= 2:
                        var_name = parts[0]
                        try:
                            value = float(parts[1])
                            results[var_name] = value
                        except ValueError:
                            results[var_name] = 0.0

        return results

    def analyze_relations(self, points: List[Dict]) -> List[str]:
        """分析所有点之间的关系"""
        # 生成完整的SMT2代码
        smt_code = self.generate_complete_smt2(points)

        # 写入文件
        file_path = self.write_smt_file(smt_code)
        print("SMT2文件已生成:", file_path)

        # 运行求解器
        success, result, output = self.run_smt_solver(file_path)

        print("求解器结果:", result)

        if not success or ("sat" not in result and "delta-sat" not in result):
            return ["分析失败: {}".format(result)]

        # 解析结果
        parsed_results = self.parse_model_output(output)

        # 格式化输出
        formatted_results = []
        for i in range(1, len(points)):
            current_point = points[i]
            found = False

            for j in range(i):
                ref_point = points[j]
                spatial_key = "spatial_{}_{}".format(current_point['id'], ref_point['id'])
                orient_key = "orient_{}_{}".format(current_point['id'], ref_point['id'])

                if spatial_key in parsed_results:
                    spatial_code = int(round(parsed_results[spatial_key]))
                    orient_code = int(round(parsed_results.get(orient_key, 0)))

                    spatial_rel = self.CODE_TO_RELATION.get(spatial_code, "unknown")
                    orient_rel = self.CODE_TO_RELATION.get(orient_code, "none")

                    if orient_rel != "none":
                        formatted_results.append("{} 在 {} 的{}方向，朝向{}".format(
                            current_point['id'], ref_point['id'], spatial_rel, orient_rel
                        ))
                    else:
                        formatted_results.append("{} 在 {} 的{}方向".format(
                            current_point['id'], ref_point['id'], spatial_rel
                        ))
                    found = True
                    break

            if not found:
                formatted_results.append("{} 与参考点无明确空间关系".format(current_point['id']))

        return formatted_results

    def print_results(self, results: List[str]):
        """打印分析结果"""
        print("=== 空间关系分析结果 ===")
        for i, result in enumerate(results, 1):
            print("{}. {}".format(i, result))


# 测试
def main():
    points = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0},
        {"id": "P2", "x": 10.0, "y": 5.0, "heading": 90.0}
    ]

    analyzer = CompleteSMT2Analyzer()
    results = analyzer.analyze_relations(points)
    analyzer.print_results(results)


if __name__ == "__main__":
    main()