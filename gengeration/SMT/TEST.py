from SMTencode import Left_of_by_range,Right_of_by_range,Ahead_of_by_range,Behind_by_range
import subprocess

# 示例：A在(0,0)，朝向0度，B在(0,15)，距离范围[10,20]



if __name__ == "__main__":

    Ahead_of_by_range(
        A_x=0,
        A_y=0,
        A_heading=0,
        B_x=0,
        B_y=15,
        output_file="Ahead_of_constraints_test1.smt2"
    )
    Ahead_of_by_range(
        A_x=0,
        A_y=0,
        A_heading=0,
        B_x=2.67857,
        B_y=15,
        output_file="Ahead_of_constraints_test2.smt2"
    )
    Ahead_of_by_range(
        A_x=0,
        A_y=0,
        A_heading=0,
        B_x=-2.63157,
        B_y=15,
        output_file="Ahead_of_constraints_test3.smt2"
    )



    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=0,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test1.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=1,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test2.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=-1,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test3.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=2,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test4.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=-2,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test5.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=3,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test6.smt2"
    # )
    #
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=-3,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test7.smt2"
    # )

    ###unsat
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=-2.67857,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test8.smt2"
    # )
    ###sat
    # Left_of_by_range(
    #     A_x=0,
    #     A_y=0,
    #     A_heading=0,
    #     B_x=-15,
    #     B_y=-2.63157,
    #     range_x=10,
    #     range_y=20,
    #     output_file="left_of_constraints_test9.smt2"
    # )
