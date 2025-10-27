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

                #声明距离（常量） 和  距离区间上下界（变量）
                dist_var = f"dist_v{i}_{ref_name}"
                dist_low = f"dist_low_v{i}_{ref_name}"
                dist_high = f"dist_high_v{i}_{ref_name}"
                # 声明
                f.write(f"(declare-const {dist_var} Real)\n")
                f.write(f"(declare-const {dist_low} Real)\n")
                f.write(f"(declare-const {dist_high} Real)\n")

                f.write(
                    f"(assert (= {dist_var} (sqrt (+ (* (- {B_x} {A_x}) (- {B_x} {A_x})) "
                    f"(* (- {B_y} {A_y}) (- {B_y} {A_y}))))))\n"
                )

                f.write(f"(assert (= {dist_high} (+ {dist_low} 5)))\n")

                rel_or_list = []
                angle_exprs = {}
                for rel_type in ['ahead','behind']:
                    if rel_type == 'ahead':
                        min_angle, max_angle = -10, 10
                    elif rel_type == 'behind':
                        min_angle, max_angle = 170, 190
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
                    f"      (and (>= local_x local_x_v{i}_{ref_name}) (<= local_x (+ local_x_v{i}_{ref_name} 5))"
                    f"           (>= local_y local_y_v{i}_{ref_name}) (<= local_y (+ local_y_v{i}_{ref_name} 5))))))"
                )
                # --- 声明 relation 整数变量 1: ahead 2:behind 3:left 4:right 5:local-x-y ---
                f.write(f"(declare-const relation_v{i}_{ref_name} Int)\n")

                # --- 4. ite 优先级约束 ---
                f.write(
                    f"(assert (ite (or {angle_exprs['ahead']} {angle_exprs['behind']} ) "
                    f"(or (= relation_v{i}_{ref_name} 1) (= relation_v{i}_{ref_name} 2) )"
                    f"(= relation_v{i}_{ref_name} 3)))\n"
                )

                # ---  蕴含约束 ---
                f.write(f"(assert (=> (= relation_v{i}_{ref_name} 5) {local_expr}))\n")

                for rel_type in ['ahead', 'behind']:
                    f.write(
                        f"(assert (=> (= relation_v{i}_{ref_name} "
                        f"{ {'ahead': 1, 'behind': 2}[rel_type]}) "
                        f"(and {angle_exprs[rel_type]} "
                        f"(>= {dist_var} {dist_low}) (<= {dist_var} {dist_high}))))\n"
                    )

                # ---   ---
                ors.append(f"(and (= pos_choice_{i} {j}) (= relation_v{i}_{ref_name} relation_v{i}_{ref_name}))")


            pos_constraints.append("(or " + " ".join(ors) + ")")
        f.write("(assert ( and \n" + "\n".join(pos_constraints) + "\n))\n\n")


        # --- 7. 检查可满足性 ---
        f.write("(check-sat)\n(get-model)\n")


if __name__ == "__main__":


    # one boundary   atan2-90度正好为0   在归一化的边界上    2.8s
    points5 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points5, "test5.smt2")

    # one boundary   atan2-90度正好为0   在归一化的边界上    1.4s
    points51 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 50.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points51, "test51.smt2")


    # one boundary   atan2-90度正好为0   在归一化的边界上 13S ego.heading _+10 跨越了0
    points52 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 10.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points52, "test52.smt2")

    # one boundary   atan2-90度正好为0   在归一化的边界上  1.4S
    points53 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 11.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points53, "test53.smt2")


    # one boundary   atan2-90度正好为0   在归一化的边界上  7.4S  ego.heading _+10 跨越了0
    points54 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": -10.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points54, "test54.smt2")

    # NO boundary   atan2-90度正好为0   在归一化的边界上  -11.0_+10 -> [-21,-1]     1s
    points55 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": -11.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points55, "test55.smt2")

    # one boundary   atan2-90度正好为0   在归一化的边界上  2.8s  ego.heading _+10 跨越了0
    points56 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 9.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points56, "test56.smt2")

    # one boundary   atan2-90 归一化为0    ego.heading +170 跨越了360   8s
    points57 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 190.0},
        {"id": "P1", "x": 0.0, "y":5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points57, "test57.smt2")

    # one boundary   atan2-90 归一化为0    ego.heading +190 跨越了360  8s
    points58 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 170.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points58, "test58.smt2")

    # one boundary   atan2-90 归一化为0    ego.heading +190 没跨越360   1.4s
    points59 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 169.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points59, "test59.smt2")


    # one boundary   atan2-90 归一化为0    ego.heading +170  [1,21]   9.5s
    points510 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 191.0},
        {"id": "P1", "x": 0.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points510, "test510.smt2")


    # one boundary   atan2-90度正好为0   在归一化的边界上      2.8s
    points6 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 0.0, "y": 10.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points6, "test6.smt2")

    # one boundary     atan2 在pi 和-pi的边界上  但后续正则化之后都是90  0.3s
    points7 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points7, "test7.smt2")

    # one boundary     atan2 在pi 和-pi的边界上  后续正则化之后都是90    但80+10=90  正好在边界上比较   0.25s
    points8 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 80.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points8, "test8.smt2")

    # one boundary     atan2 在pi 和-pi的边界上  后续正则化之后都是90    但100-10=90  正好在边界上比较   0.25s
    points9 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 80.0},
        {"id": "P1", "x": -5.0, "y": 0.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points9, "test9.smt2")

    # one boundary     215+170=385=25  215+190=405=45
    points10 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 215.0},
        {"id": "P1", "x": -5.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points10, "test10.smt2")



    # no boundary  0.3s
    points1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 5.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points1, "test1.smt2")

    # no boundary    0.3s
    points2 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": 5.0, "y": -5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points2, "test2.smt2")

    # no boundary  0.3s
    points3 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": -5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points3, "test3.smt2")


    # no boundary  0.3s
    points4 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 0.0},
        {"id": "P1", "x": -5.0, "y": 5.0, "heading": 0.0}
    ]
    generate_complete_smt_dreal(points4, "test4.smt2")
