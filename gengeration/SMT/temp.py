import math
import subprocess
import os
from typing import List, Dict, Optional


class SMTRelationAnalyzer:
    """
    基于SMT的点序列关系分析器（保留完整功能）
    """

    def __init__(self, temp_dir: str = "./temp_smt"):
        self.temp_dir = temp_dir
        os.makedirs(temp_dir, exist_ok=True)
        self.dreal_path = "/opt/dreal/4.21.06.2/bin/dreal"

    def _generate_spatial_smt(self, relation_type: str, ref_point: Dict, target_point: Dict) -> str:
        """生成空间关系SMT约束（完全SMT计算）"""
        angle_ranges = {
            'left': (80, 100),
            'right': (260, 280),
            'ahead': (-10, 10),
            'behind': (170, 190)
        }
        min_angle, max_angle = angle_ranges[relation_type]

        smt_code = f"""; 空间关系{relation_type}的SMT约束
(set-logic QF_NRA)

; 输入点定义
(declare-const ref_x Real)
(declare-const ref_y Real)
(declare-const ref_heading Real)
(declare-const target_x Real)
(declare-const target_y Real)

; 设置已知值
(assert (= ref_x {ref_point['x']}))
(assert (= ref_y {ref_point['y']}))
(assert (= ref_heading {ref_point['heading']}))
(assert (= target_x {target_point['x']}))
(assert (= target_y {target_point['y']}))

; 计算相对坐标
(define-fun delta_x () Real (- target_x ref_x))
(define-fun delta_y () Real (- target_y ref_y))

; 计算相对于参考点朝向的角度
(define-fun angle_rad () Real 
    (- (atan2 delta_y delta_x) (* ref_heading (/ {math.pi} 180.0))))
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化
(define-fun normalize_angle ((angle Real)) Real
    (let ((full_circle 360.0))
        (ite (>= angle full_circle) (- angle full_circle)
             (ite (< angle 0.0) (+ angle full_circle)
                  angle))))

(define-fun normalized_angle () Real (normalize_angle angle_deg))

; 角度约束
(define-fun angle_constraint () Bool
    (let ((min_angle {min_angle}.0)
          (max_angle {max_angle}.0))
        (ite (<= min_angle max_angle)
            (and (>= normalized_angle min_angle) (<= normalized_angle max_angle))
            (or (>= normalized_angle min_angle) (<= normalized_angle max_angle)))))

(assert angle_constraint)
(check-sat)
(get-model)
"""
        return smt_code

    def _generate_orientation_smt(self, relation_type: str, ref_point: Dict, target_point: Dict) -> str:
        """生成朝向关系SMT约束（完全SMT计算）"""
        smt_code = f"""; 朝向关系{relation_type}的SMT约束
(set-logic QF_NRA)

; 输入点定义
(declare-const ref_x Real)
(declare-const ref_y Real)
(declare-const ref_heading Real)
(declare-const target_x Real)
(declare-const target_y Real)
(declare-const target_heading Real)

; 设置已知值
(assert (= ref_x {ref_point['x']}))
(assert (= ref_y {ref_point['y']}))
(assert (= ref_heading {ref_point['heading']}))
(assert (= target_x {target_point['x']}))
(assert (= target_y {target_point['y']}))
(assert (= target_heading {target_point['heading']}))

; 计算相对坐标
(define-fun delta_x_toward () Real (- ref_x target_x))
(define-fun delta_y_toward () Real (- ref_y target_y))
(define-fun delta_x_away () Real (- target_x ref_x))
(define-fun delta_y_away () Real (- target_y ref_y))

; 计算方位角
(define-fun bearing_toward_rad () Real (atan2 delta_y_toward delta_x_toward))
(define-fun bearing_away_rad () Real (atan2 delta_y_away delta_x_away))

; 转换为相对于正Y轴的角度（度）
(define-fun bearing_toward_deg () Real 
    (* (- (/ {math.pi} 2.0) bearing_toward_rad) (/ 180.0 {math.pi})))
(define-fun bearing_away_deg () Real 
    (* (- (/ {math.pi} 2.0) bearing_away_rad) (/ 180.0 {math.pi})))

; 角度规范化
(define-fun normalize_angle ((angle Real)) Real
    (let ((full_circle 360.0))
        (ite (>= angle full_circle) (- angle full_circle)
             (ite (< angle 0.0) (+ angle full_circle)
                  angle))))

(define-fun normalized_bearing_toward () Real (normalize_angle bearing_toward_deg))
(define-fun normalized_bearing_away () Real (normalize_angle bearing_away_deg))
(define-fun normalized_target_heading () Real (normalize_angle target_heading))

; 计算角度差
(define-fun angle_diff_toward () Real 
    (normalize_angle (- normalized_bearing_toward normalized_target_heading)))
(define-fun angle_diff_away () Real 
    (normalize_angle (- normalized_bearing_away normalized_target_heading)))
(define-fun angle_diff_parallel () Real 
    (normalize_angle (- ref_heading target_heading)))

; 取最小角度差
(define-fun min_diff ((angle Real)) Real
    (ite (> angle 180.0) (- 360.0 angle) angle))

; 朝向约束
(define-fun toward_constraint () Bool (<= (min_diff angle_diff_toward) 10.0))
(define-fun away_constraint () Bool (<= (min_diff angle_diff_away) 10.0))
(define-fun parallel_constraint () Bool 
    (let ((diff (min_diff angle_diff_parallel)))
        (or (<= diff 10.0) (>= diff 170.0))))

; 根据关系类型选择约束
(assert (
    {"toward_constraint" if relation_type == 'toward' else
        "away_constraint" if relation_type == 'away' else
        "parallel_constraint"}
))

(check-sat)
(get-model)
"""
        return smt_code

    def _run_smt_solver(self, smt_code: str) -> bool:
        """运行SMT求解器"""
        file_path = os.path.join(self.temp_dir, "temp_relation.smt2")
        with open(file_path, "w") as f:
            f.write(smt_code)

        try:
            result = subprocess.run(
                [self.dreal_path, file_path],
                capture_output=True,
                text=True,
                timeout=5
            )
            output = result.stdout.strip().lower()
            return "sat" in output or "delta-sat" in output
        except:
            return False

    def check_spatial_relation(self, relation_type: str, ref_point: Dict, target_point: Dict) -> bool:
        """检查空间位置关系"""
        smt_code = self._generate_spatial_smt(relation_type, ref_point, target_point)
        return self._run_smt_solver(smt_code)

    def check_orientation_relation(self, relation_type: str, ref_point: Dict, target_point: Dict) -> bool:
        """检查朝向关系"""
        smt_code = self._generate_orientation_smt(relation_type, ref_point, target_point)
        return self._run_smt_solver(smt_code)

    def find_closest_reference(self, current_point: Dict, reference_points: List[Dict]) -> Dict:
        """找到最近的参考点（使用SMT计算距离）"""
        if not reference_points:
            raise ValueError("Reference points list is empty")

        # 简单实现，实际可以也用SMT计算
        def distance(p1, p2):
            return math.sqrt((p1['x'] - p2['x']) ** 2 + (p1['y'] - p2['y']) ** 2)

        return min(reference_points, key=lambda p: distance(p, current_point))

    def analyze_point_relations(self, current_point: Dict, reference_points: List[Dict],
                                use_closest_only: bool = True) -> Optional[str]:
        """分析当前点与参考点的关系"""
        if use_closest_only:
            ref_point = self.find_closest_reference(current_point, reference_points)
            relations = self._get_all_spatial_relations(ref_point, current_point)
            if relations:
                return self._format_relation_result(current_point['id'], ref_point['id'], relations)

            # 检查其他参考点
            for other_ref in [p for p in reference_points if p['id'] != ref_point['id']]:
                relations = self._get_all_spatial_relations(other_ref, current_point)
                if relations:
                    return self._format_relation_result(current_point['id'], other_ref['id'], relations)
        else:
            # 检查所有参考点
            for ref_point in reference_points:
                relations = self._get_all_spatial_relations(ref_point, current_point)
                if relations:
                    return self._format_relation_result(current_point['id'], ref_point['id'], relations)

        return f"{current_point['id']} has no defined spatial relation with reference points"

    def _get_all_spatial_relations(self, ref_point: Dict, target_point: Dict) -> List[str]:
        """获取所有满足的空间关系"""
        relations = []
        for rel in ['left', 'right', 'ahead', 'behind']:
            if self.check_spatial_relation(rel, ref_point, target_point):
                relations.append(rel)
        return relations

    def _format_relation_result(self, target_id: str, ref_id: str, relations: List[str]) -> str:
        """格式化关系结果"""
        relation_str = "/".join(relations).upper()
        return f"{target_id} is {relation_str} of {ref_id}"

    def analyze_sequence(self, points: List[Dict], use_closest_only: bool = True) -> List[str]:
        """分析点序列（保留原始功能）"""
        if len(points) < 2:
            return ["Need at least ego and one point to analyze"]

        results = []
        for i in range(1, len(points)):
            current_point = points[i]
            reference_points = points[:i]
            relation = self.analyze_point_relations(current_point, reference_points, use_closest_only)
            results.append(relation)
        return results

    def analyze_orientation_relations(self, points: List[Dict]) -> List[str]:
        """分析点序列的朝向关系"""
        results = []
        for i in range(len(points)):
            for j in range(len(points)):
                if i != j:
                    A_point = points[i]
                    B_point = points[j]
                    relation = self._get_orientation_relation(A_point, B_point)
                    if relation:
                        results.append(f"{B_point['id']} is {relation} {A_point['id']}")
        return results

    def _get_orientation_relation(self, ref_point: Dict, target_point: Dict) -> Optional[str]:
        """获取朝向关系"""
        for rel in ['toward', 'away', 'parallel']:
            if self.check_orientation_relation(rel, ref_point, target_point):
                return rel
        return None

    def analyze_combined_relations(self, points: List[Dict]) -> List[str]:
        """综合分析空间位置和朝向关系"""
        spatial_results = self.analyze_sequence(points)
        orientation_results = self.analyze_orientation_relations(points)
        return spatial_results + orientation_results


# 使用示例
if __name__ == "__main__":
    analyzer = SMTRelationAnalyzer()

    # 定义点序列（第一个点是ego）
    points = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 90.0},
        {"id": "P1", "x": 5.0, "y": 0.0, "heading": 90.0},
        {"id": "P2", "x": 10.0, "y": -2.0, "heading": 90.0},
        {"id": "P3", "x": 8.0, "y": 3.0, "heading": 90.0},
        {"id": "P4", "x": 15.0, "y": 0.0, "heading": 90.0}
    ]

    print("=== 空间关系分析 ===")
    spatial_results = analyzer.analyze_sequence(points)
    for i, result in enumerate(spatial_results, 1):
        print(f"{i}. {result}")

    print("\n=== 朝向关系分析 ===")
    orientation_results = analyzer.analyze_orientation_relations(points)
    for i, result in enumerate(orientation_results, 1):
        print(f"{i}. {result}")

    print("\n=== 综合分析 ===")
    combined_results = analyzer.analyze_combined_relations(points)
    for i, result in enumerate(combined_results, 1):
        print(f"{i}. {result}")