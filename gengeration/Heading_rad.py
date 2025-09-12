import math
from pyquaternion import Quaternion
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
    heading_angle = heading*(360/(2*math.pi))

    return heading_angle

# ego_quaternion = Quaternion(-0.20417118914766993, 0.013443067088213643, -0.01259805204385892, -0.978761819113306)
# heading_rad = quaternion_to_2d_heading(ego_quaternion)
#
#
# car1_quaternion = Quaternion(0.2017020617620692, 0.0, 0.0, 0.9794469246880764)
# car1_rad = quaternion_to_2d_heading(car1_quaternion)
#
# print('ego:', heading_rad)
# print('ca1:', car1_rad)