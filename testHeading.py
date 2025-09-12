import math
from pyquaternion import Quaternion
# def quaternion_to_2d_heading(q):
#     """将四元数转换为二维航向角（正北为0°，正西为90°）"""
#     # 将四元数转换为欧拉角（roll, pitch, yaw），单位为弧度
#     yaw_3d = q.yaw_pitch_roll[2]  # 假设四元数基于ENU坐标系（东-北-天）
#
#     # 坐标校正：将航向角从正东为0°转换为正北为0°
#     # 原欧拉角定义：0°指向东，逆时针增加
#     # 目标定义：0°指向北，逆时针增加（正西为90°）
#     heading = (yaw_3d + math.pi / 2) % (2 * math.pi)
#     return heading
def quaternion_to_2d_heading(q):
    """将四元数转换为二维航向角（正北为0°，正西为90°）"""
    # 确保四元数已归一化
    q = q.normalised

    # 直接计算偏航角(yaw)
    # 四元数分量 (w, x, y, z)
    w, x, y, z = q.elements

    # 计算偏航角(yaw) - 使用atan2确保正确的角度范围
    yaw = math.atan2(2 * (w * z + x * y), 1 - 2 * (y * y + z * z))

    # 坐标转换：从ENU坐标系（东为0°）到正北为0°
    heading = (yaw + math.pi / 2) % (2 * math.pi)

    return heading


ego_quaternion = Quaternion(-0.20417118914766993, 0.013443067088213643, -0.01259805204385892, -0.978761819113306)
heading_rad = quaternion_to_2d_heading(ego_quaternion)

car1_quaternion = Quaternion(0.2017020617620692, 0.0, 0.0, 0.9794469246880764)
car1_rad = quaternion_to_2d_heading(car1_quaternion)

print('ego:', heading_rad)
print('ca1:', car1_rad)



quaternion1 = Quaternion(0.24777690872566385,  0.0, 0.0, 0.9688171156117928)
quaternion1_rad = quaternion_to_2d_heading(quaternion1)
print(quaternion1_rad)

quaternion2 = Quaternion(-0.4760617039807454,  0.0, 0.0, 0.8794118796121355)
quaternion2_rad = quaternion_to_2d_heading(quaternion2)
print(quaternion2_rad)