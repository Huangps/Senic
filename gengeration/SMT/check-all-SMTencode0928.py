import math

def generate_complete_smt_dreal(points, filename):
    ego = points[0]
    others = points[1:]
    m = len(others)

    with open(filename, "w") as f:
        f.write("(set-logic QF_NRA)\n\n")

        # --- 1. 声明 ego ---
        f.write(f"(declare-const x0 Real) (assert (= x0 {ego['x']}))\n")
        f.write(f"(declare-const y0 Real) (assert (= y0 {ego['y']}))\n")
        f.write(f"(declare-const h0 Real) (assert (= h0 {ego['heading']}))\n\n")

        # --- 2. 声明非ego点 ---
        for i, pt in enumerate(others, 1):
            f.write(f"(declare-const x{i} Real) (assert (= x{i} {pt['x']}))\n")
            f.write(f"(declare-const y{i} Real) (assert (= y{i} {pt['y']}))\n")
            f.write(f"(declare-const h{i} Real) (assert (= h{i} {pt['heading']}))\n\n")


        # 声明所有相对角度变量


        # --- 3. 布尔矩阵编码排列 ---
        f.write("; ==== 布尔矩阵排列 ====\n")
        for i in range(m):  # 位置 i
            for j in range(m):  # 点 j
                f.write(f"(declare-const b_{i}_{j} Bool)\n")
        f.write("\n")

        # 每个位置选一个点
        for i in range(m):
            ors = " ".join([f"b_{i}_{j}" for j in range(m)])
            f.write(f"(assert (or {ors}))\n")
        f.write("\n")

        # 每个点只能出现一次
        for j in range(m):
            for i1 in range(m):
                for i2 in range(i1+1, m):
                    f.write(f"(assert (not (and b_{i1}_{j} b_{i2}_{j})))\n")
        f.write("\n")

        # --- 4. 定义排列后的非ego点属性 ---
        for i in range(m):
            expr_x = "".join([f"(ite b_{i}_{j} x{j+1} " for j in range(m)]) + f"x{m}" + ")"*m
            expr_y = "".join([f"(ite b_{i}_{j} y{j+1} " for j in range(m)]) + f"y{m}" + ")"*m
            expr_h = "".join([f"(ite b_{i}_{j} h{j+1} " for j in range(m)]) + f"h{m}" + ")"*m
            f.write(f"(define-fun vx{i} () Real {expr_x})\n")
            f.write(f"(define-fun vy{i} () Real {expr_y})\n")
            f.write(f"(define-fun vh{i} () Real {expr_h})\n\n")




        # --- 5. 生成位置关系约束 (前、后、左、右、局部) ---
        f.write("; ==== 位置关系约束 ====\n")
        pos_constraints = []
        for i in range(m):
            ors = []
            for j in range(i+1):
                if j == 0:
                    A_x, A_y, A_h = "x0", "y0", "h0"
                    ref_name = "ego"
                else:
                    A_x, A_y, A_h = f"vx{j-1}", f"vy{j-1}", f"vh{j-1}"
                    ref_name = f"v{j - 1}"
                B_x, B_y = f"vx{i}", f"vy{i}"
                # 直接展开公式，不用 let
                rel_or_list = []
                for rel_type in ['ahead','behind','left','right']:
                    if rel_type == 'ahead':
                        min_angle, max_angle = -10, 10
                    elif rel_type == 'behind':
                        min_angle, max_angle = 170, 190
                    elif rel_type == 'left':
                        min_angle, max_angle = 80, 100
                    elif rel_type == 'right':
                        min_angle, max_angle = 260, 280
                    angle_expr = f"(let ((angle_deg (* (- (atan2 (- {B_y} {A_y}) (- {B_x} {A_x})) (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))" \
                                 f"(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))" \
                                 f"(let ((theta_min (+ {A_h} {min_angle})))" \
                                 f"(let ((theta_max (+ {A_h} {max_angle})))" \
                                 f"(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))" \
                                 f"(or (>= norm_angle theta_min) (<= norm_angle theta_max)))))))"
                    rel_or_list.append(angle_expr)
                # 局部坐标系 [x,x+5]@[y,y+5]


                f.write(f"(declare-const local_x_v{i}_{ref_name} Real)\n")
                f.write(f"(assert (and (>= local_x_v{i}_{ref_name} -100.0) (<= local_x_v{i}_{ref_name} 100.0)))\n")
                f.write(f"(declare-const local_y_v{i}_{ref_name} Real)\n")
                f.write(f"(assert (and (>= local_y_v{i}_{ref_name} -100.0) (<= local_y_v{i}_{ref_name} 100.0)))\n")

                local_expr = (
                    f"(let ((delta_x_global (- {B_x} {A_x}))"
                    f"      (delta_y_global (- {B_y} {A_y})))"
                    f"  (let ((heading_rad (* {A_h} (/ {math.pi} 180.0))))"
                    f"    (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global) "
                    f"(* (cos heading_rad) delta_x_global)))"
                    f"          (local_y (+ (* (sin heading_rad) delta_x_global) "
                    f"(* (cos heading_rad) delta_y_global))))"
                    f"      (and (>= local_x local_x_v{i}_{ref_name}) (<= local_x (+ local_x_v{i}_{ref_name} 0.1))"
                    f"           (>= local_y local_y_v{i}_{ref_name}) (<= local_y (+ local_y_v{i}_{ref_name} 0.1))))))"
                )

                rel_or_list.append(local_expr)
                ors.append("(or " + " ".join(rel_or_list) + ")")
            pos_constraints.append("(or " + " ".join(ors) + ")")
        f.write("(assert (and\n" + "\n".join(pos_constraints) + "\n))\n\n")

        # --- 6. 生成朝向关系约束 (朝向、背向、相对角度) ---
        f.write("; ==== 朝向关系约束 ====\n")
        # ==== 朝向关系约束 ====
        head_constraints = []
        for i in range(m):
            ors = []
            for j in range(i + 1):
                if j == 0:
                    A_x, A_y, A_h = "x0", "y0", "h0"
                    ref_name = "ego"  # ego 点
                else:
                    A_x, A_y, A_h = f"vx{j - 1}", f"vy{j - 1}", f"vh{j - 1}"
                    ref_name = f"v{j - 1}"  # 非 ego 的第 j-1 个点

                B_x, B_y, B_h = f"vx{i}", f"vy{i}", f"vh{i}"

                f.write(f"(declare-const relative_angle_v{i}_{ref_name} Real)\n")
                f.write(f"(assert (and (>= relative_angle_v{i}_{ref_name} 0.0) (<= relative_angle_v{i}_{ref_name} 360.0)))\n")

                # toward
                toward_expr = (
                    f"(let ((delta_x (- {A_x} {B_x})))"
                    f"  (let ((delta_y (- {A_y} {B_y})))"
                    f"    (let ((angle_rad (atan2 delta_y delta_x)))"
                    f"      (let ((bearing_deg (* (- angle_rad (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))"
                    f"        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) "
                    f"(ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))"
                    f"          (let ((angle_diff (- norm_bearing {B_h})))"
                    f"            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))"
                    f"              (<= min_angle_diff 10.0) )))))))"
                )


                # away
                away_expr = (
                    f"(let ((delta_x (- {B_x} {A_x})))"
                    f"  (let ((delta_y (- {B_y} {A_y})))"
                    f"    (let ((angle_rad (atan2 delta_y delta_x)))"
                    f"      (let ((bearing_deg (* (- angle_rad (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))"
                    f"        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) "
                    f"(ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))"
                    f"          (let ((angle_diff (- norm_bearing {B_h})))"
                    f"            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))"
                    f"              (<= min_angle_diff 10.0) )))))))"
                )

                relative_expr = (
                    f"(let ((rel_heading (- {B_h} {A_h})))"
                    f"  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) "
                    f"(ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))"
                    f"    (and (>= norm_rel (- relative_angle_v{i}_{ref_name} 5)) "
                    f"(<= norm_rel (+ relative_angle_v{i}_{ref_name} 5)) " # 角度差是正负5
                    f"(>= relative_angle_v{i}_{ref_name} 0) "
                    f"(< relative_angle_v{i}_{ref_name} 360))))"
                )


                ors.append(f"(or {toward_expr} {away_expr} {relative_expr})")

            head_constraints.append("(or " + " ".join(ors) + ")")

        f.write("(assert (and\n" + "\n".join(head_constraints) + "\n))\n\n")

        # --- 7. 检查可满足性 ---
        f.write("(check-sat)\n(get-model)\n")


if __name__ == "__main__":

    ##2s  two-points-test_2_1
    points_2_1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 180.0},
        {"id": "P1", "x": 5.0, "y": 5.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_1, "two-points-test_2_1.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_1.smt2")

    ##2s  two-points-test_2_2
    points_2_2 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 180.0},
        {"id": "P1", "x": 5.0, "y": 5.1, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_2, "two-points-test_2_2.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_2.smt2")


    ## long time(22min)   two-points-test_2_3
    points_2_3 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 180.0},
        {"id": "P1", "x": 0.0, "y": 1.41, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_3, "two-points-test_2_3.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_3.smt2")

    ## long time   two-points-test_2_4  只求解位置关系大约9s    只求解朝向关系0.1s以内
    points_2_4 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 180.0},
        {"id": "P1", "x": 0.0, "y": 1.4, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_4, "two-points-test_2_4.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_4.smt2")

    ## 2s   two-points-test_2_5
    points_2_5 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 2.0, "y": 3.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_5, "two-points-test_2_5.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_5.smt2")

    ## 2s   atan2(4,1)约为75度
    points_2_6 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 4.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_6, "two-points-test_2_6.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_6.smt2")

    #  2s  atan2(6,1)约为80.5度
    points_2_8 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 6.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_8, "two-points-test_2_8.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_8.smt2")


    #  2s  atan2(1000,1)约为89.94度
    points_2_12 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 1000.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_12, "two-points-test_2_12.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_12.smt2")

    # 2s
    points_2_13 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.01, "y": 100000.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_13, "two-points-test_2_13.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_13.smt2")


    #33min
    points_2_14 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_14, "two-points-test_2_14.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_14.smt2")


    #1.5s
    points_2_15 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": -5.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_15, "two-points-test_2_15.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_15.smt2")

    # 1.3s
    points_2_16 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 5.0, "y": 0.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_16, "two-points-test_2_16.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_16.smt2")

    # 1.3s
    points_2_17 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_17, "two-points-test_2_17.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_17.smt2")

    # 5s
    points_2_18 = [
        {"id": "ego", "x": 1.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_18, "two-points-test_2_18.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_18.smt2")


    ##    three-points-test_3_1.smt2
    points_3_1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 180.0},
        {"id": "P1", "x": 5.0, "y": 5.0, "heading": 0.0},
        {"id": "P2", "x": 15.0, "y": 5.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_3_1, "three-points-test_3_1.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: three-points-test_3_1.smt2")

    ##    three-points-test_3_2.smt2
    points_3_2= [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 1.0, "heading": 0.0},
        {"id": "P2", "x": -1.0, "y": 1.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_3_2, "three-points-test_3_2.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: three-points-test_3_2.smt2")