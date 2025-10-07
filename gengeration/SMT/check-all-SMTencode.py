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

        # 每个位置至少选一个点（行约束）
        for i in range(m):
            ors = " ".join([f"b_{i}_{j}" for j in range(m)])
            f.write(f"(assert (or {ors}))\n")
        f.write("\n")

        # 每个位置最多选一个点（行约束）
        for i in range(m):
            for j1 in range(m):
                for j2 in range(j1 + 1, m):
                    f.write(f"(assert (not (and b_{i}_{j1} b_{i}_{j2})))\n")
        f.write("\n")

        # 每个点最多出现在一个位置（列约束）
        for j in range(m):
            for i1 in range(m):
                for i2 in range(i1 + 1, m):
                    f.write(f"(assert (not (and b_{i1}_{j} b_{i2}_{j})))\n")
        f.write("\n")

        # 每个点至少出现在一个位置（列约束）
        for j in range(m):
            ors = " ".join([f"b_{i}_{j}" for i in range(m)])
            f.write(f"(assert (or {ors}))\n")
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

            # 声明选择变量，表示当前点 vx{i} 是和哪个参考点有关系
            f.write(f"(declare-const pos_choice_{i} Int)\n")
            f.write(f"(assert (and (>= pos_choice_{i} 0) (<= pos_choice_{i} {i})))\n")

            for j in range(i+1):
                if j == 0:
                    A_x, A_y, A_h = "x0", "y0", "h0"
                    ref_name = "ego"
                else:
                    A_x, A_y, A_h = f"vx{j-1}", f"vy{j-1}", f"vh{j-1}"
                    ref_name = f"v{j - 1}"
                B_x, B_y = f"vx{i}", f"vy{i}"


                rel_or_list = []
                angle_exprs = {}
                for rel_type in ['ahead','behind','left','right']:
                    if rel_type == 'ahead':
                        min_angle, max_angle = -10, 10
                    elif rel_type == 'behind':
                        min_angle, max_angle = 170, 190
                    elif rel_type == 'left':
                        min_angle, max_angle = 80, 100
                    elif rel_type == 'right':
                        min_angle, max_angle = 260, 280
                    # angle_expr = f"(let ((angle_deg (* (- (atan2 (- {B_y} {A_y}) (- {B_x} {A_x})) (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))" \
                    #              f"(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))" \
                    #              f"(let ((theta_min (+ {A_h} {min_angle})))" \
                    #              f"(let ((theta_max (+ {A_h} {max_angle})))" \
                    #              f"(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))" \
                    #              f"(or (>= norm_angle theta_min) (<= norm_angle theta_max)))))))"

                    angle_expr = f"(let ((angle_deg (* (- (atan2 (- {B_y} {A_y}) (- {B_x} {A_x})) (/ {math.pi} 2.0)) (/ 180.0 {math.pi}))))" \
                                 f"(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))" \
                                 f"(let ((theta_min (let ((raw (+ {A_h} {min_angle}))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))" \
                                 f"(let ((theta_max (let ((raw (+ {A_h} {max_angle}))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))" \
                                 f"(ite (<= theta_min theta_max)" \
                                 f"(and (>= norm_angle theta_min) (<= norm_angle theta_max))" \
                                 f"(or (>= norm_angle theta_min) (<= norm_angle theta_max)))))))"



                    angle_exprs[rel_type] = angle_expr
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

                # --- 声明 relation 整数变量 1: ahead 2:behind 3:left 4:right 5:local-x-y ---
                f.write(f"(declare-const relation_v{i}_{ref_name} Int)\n")

                # --- 4. ite 优先级约束 ---
                f.write(
                    f"(assert (ite (or {angle_exprs['ahead']} {angle_exprs['behind']} "
                    f"{angle_exprs['left']} {angle_exprs['right']}) "
                    f"(or (= relation_v{i}_{ref_name} 1) (= relation_v{i}_{ref_name} 2) "
                    f"(= relation_v{i}_{ref_name} 3) (= relation_v{i}_{ref_name} 4)) "
                    f"(= relation_v{i}_{ref_name} 5)))\n"
                )

                # ---  蕴含约束 ---
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 1) {angle_exprs['ahead']}))\n")
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 2) {angle_exprs['behind']}))\n")
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 3) {angle_exprs['left']}))\n")
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 4) {angle_exprs['right']}))\n")
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 5) {local_expr}))\n")

                # ---   ---
                ors.append(f"(and (= pos_choice_{i} {j}) (= relation_v{i}_{ref_name} relation_v{i}_{ref_name}))")


            pos_constraints.append("(or " + " ".join(ors) + ")")
        f.write("(assert ( and \n" + "\n".join(pos_constraints) + "\n))\n\n")


        # --- 6. 生成朝向关系约束 (朝向、背向、相对角度) ---
        f.write("; ==== 朝向关系约束 ====\n")
        # ==== 朝向关系约束 ====
        head_constraints = []
        for i in range(m):
            ors = []

            # 声明选择变量，表示当前点 vx{i} 是和哪个参考点有朝向关系
            f.write(f"(declare-const head_choice_{i} Int)\n")
            f.write(f"(assert (and (>= head_choice_{i} 0) (<= head_choice_{i} {i})))\n")


            for j in range(i + 1):
                if j == 0:
                    A_x, A_y, A_h = "x0", "y0", "h0"
                    ref_name = "ego"  # ego 点
                else:
                    A_x, A_y, A_h = f"vx{j - 1}", f"vy{j - 1}", f"vh{j - 1}"
                    ref_name = f"v{j - 1}"  # 非 ego 的第 j-1 个点

                B_x, B_y, B_h = f"vx{i}", f"vy{i}", f"vh{i}"


                # 关系类型：1=toward, 2=away, 3=relative
                f.write(f"(declare-const head_relation_v{i}_{ref_name} Int)\n")
                f.write(
                    f"(assert (and (>= head_relation_v{i}_{ref_name} 1) (<= head_relation_v{i}_{ref_name} 3)))\n")

                # 相对角度变量（只在 relative 时使用）
                f.write(f"(declare-const relative_angle_v{i}_{ref_name} Real)\n")
                f.write(
                    f"(assert (and (>= relative_angle_v{i}_{ref_name} 0.0) (<= relative_angle_v{i}_{ref_name} 360.0)))\n")

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

                # 蕴含约束
                f.write(f"(assert (=> (= head_relation_v{i}_{ref_name} 1) {toward_expr}))\n")
                f.write(f"(assert (=> (= head_relation_v{i}_{ref_name} 2) {away_expr}))\n")
                f.write(f"(assert (=> (= head_relation_v{i}_{ref_name} 3) {relative_expr}))\n")

                # 优先级 ite（toward/away 优先，如果都不行才允许 relative）
                f.write(
                    f"(assert (ite (or {toward_expr} {away_expr}) "
                    f"(or (= head_relation_v{i}_{ref_name} 1) (= head_relation_v{i}_{ref_name} 2)) "
                    f"(= head_relation_v{i}_{ref_name} 3)))\n"
                )

                # 加入到 or-list
                ors.append(
                    f"(and (= head_choice_{i} {j}) "
                    f"(or (= head_relation_v{i}_{ref_name} 1) (= head_relation_v{i}_{ref_name} 2) (= head_relation_v{i}_{ref_name} 3)))"
                )

            head_constraints.append("(or " + " ".join(ors) + ")")

        f.write("(assert (and\n" + "\n".join(head_constraints) + "\n))\n\n")

        # --- 7. 检查可满足性 ---
        f.write("(check-sat)\n(get-model)\n")


if __name__ == "__main__":

    ## 138min two-points-test_2_1_new
    points_2_1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 315.0},
        {"id": "P1", "x": 5.0, "y": 5.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_1, "two-points-test_2_1_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_1_new.smt2")

    #  6s
    points_2_2 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 5.0, "y": 0.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_2, "two-points-test_2_2_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_2_new.smt2")


    #  3s
    points_2_3 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_3, "two-points-test_2_3_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_3_new.smt2")

    # 48
    points_2_4 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 270.0}
    ]

    generate_complete_smt_dreal(points_2_4, "two-points-test_2_4_new.smt2")
    print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_4_new.smt2")



    #
    points_2_5 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_5, "two-points-test_2_5_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_5_new.smt2")

    #
    points_2_6 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 5.0, "heading": 0.0}
    ]

    #generate_complete_smt_dreal(points_2_6, "two-points-test_2_6_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_6_new.smt2")

    #
    points_2_7 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]


    points_2_8 = [
        {"id": "ego", "x": 1.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 1.0, "y": 5.0, "heading": 0.0}
    ]
    #generate_complete_smt_dreal(points_2_8, "two-points-test_2_8_new.smt2")
    #print("已生成 dReal 可用的完整 SMT-LIB 文件: two-points-test_2_8_new.smt2")



    #
    points_4_1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 270.0},
        {"id": "P2", "x": -5.0, "y": 0.0, "heading": 270.0},
        {"id": "P3", "x": -5.0, "y": 0.0, "heading": 270.0}
    ]

    #generate_complete_smt_dreal(points_4_1, "three-points-test_4_1.smt2")
   # print("已生成 dReal 可用的完整 SMT-LIB 文件: three-points-test_3_1_new.smt2")





    # ==== 位置关系约束 ====

