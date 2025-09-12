import math
from pyquaternion import Quaternion
from nuscenes.nuscenes import NuScenes

from nuimages import NuImages


from nuscenes.utils.data_classes import Box
import numpy as np
# 初始化数据集
nuim = NuImages(
    version='v1.0-all',
    #dataroot='D:/Scenic-main/nuscenesData/v1.0-all/',
    dataroot='D:/Scenic-main/nuscenesData/',
    verbose=False
)


# 这里根据图片获得的sample_data就是一个特定传感器的数据，前车前摄像头、车顶雷达等，具体是哪个传感器根据传进去的图片名确定
# sample_data  内有sample_token关键字，对应一个sample，sample是sample_data的上一层数据，sample包含所有的传感器
# 当前图片对应的sample_data

def get_ego_from_fig(filename: str):
    """
    获取自车状态信息
    返回字典  位置(3元组)：ego_position 和  heading(4元组)：ego_rotation
    """

    current_fig_sample_data = next((sd for sd in nuim.sample_data
                        if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")
    ego_pose = nuim.get('ego_pose', current_fig_sample_data['ego_pose_token'])

    return {
        'ego_position': ego_pose['translation'],
        'ego_rotation': ego_pose['rotation']
    }


def get_sensor_from_fig(filename: str):
    """
    返回当前图片对应的传感器类型， 如camera、lidar
    """
    current_fig_sample_data = next((sd for sd in nuim.sample_data
                                    if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")
    return current_fig_sample_data['sensor_modality']



def get_all_object_from_fig(filename: str):
    """
    获取场景中所有目标信息
    不仅限于当前传感器(即不仅限于当前sample_data)
    返回objects数组，每个元素有'type'、'position'、'size'三个属性
    """
    current_fig_sample_data = next((sd for sd in nuim.sample_data
                        if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")

    # 当前图片所属的sample：
    sample_token = current_fig_sample_data['sample_token']
    sample = nusc.get('sample', sample_token)

    # 提取检测目标
    objects = []
    for ann_token in sample['anns']:
        ann = nusc.get('sample_annotation', ann_token)
        objects.append({
            'type': ann['category_name'],
            'position': ann['translation'],  # [x, y, z]
            'size': ann['size'],  # [长, 宽, 高]
            'rotation': ann['rotation'],  # [长, 宽, 高]
        })

    return objects


def get_scene_location_from_fig(filename: str):
    """
    获取场景中位置信息，即四张地图的那一张
    """
    current_fig_sample_data = next((sd for sd in nuim.sample_data
                        if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")


    sample = nuim.get('sample', current_fig_sample_data['sample_token'])
    scene = nuim.get('scene', sample['scene_token'])
    log = nuim.get('log', scene['log_token'])

    return log['location']


def render_annotation(filename: str, index: int, out_path: str):
    """
    渲染sample中的第index+1个标注
    """
    current_fig_sample_data = next((sd for sd in nuim.sample_data
                        if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")

    sample_token = current_fig_sample_data['sample_token']
    sample = nuim.get('sample', sample_token)


    my_annotation_token = sample['anns'][index]
    my_annotation_metadata = nuim.get('sample_annotation', my_annotation_token)

    nuim.render_annotation(my_annotation_metadata['token'], extra_info=True, out_path=out_path)





def render_fig(filename: str):
    """渲染指定图片"""
    current_fig_sample_data = next((sd for sd in nuim.sample_data
                                    if filename in sd['filename']), None)
    if not current_fig_sample_data:
        raise FileNotFoundError(f"未找到文件 {filename}")
    nuim.render_sample_data(current_fig_sample_data['token']) # 渲染当前图片

def calculate_2D_distance(ego_translation: list, obj_translation: list) -> float:
    """计算目标到自车的平面距离,忽略Z轴"""
    # 提取前两个维度（x,y）并转换为数组
    ego_xy = np.array(ego_translation[:2])
    obj_xy = np.array(obj_translation[:2])
    return np.linalg.norm(ego_xy - obj_xy)

def calculate_3D_distance(ego_translation: list, obj_translation: list) -> float:
    """计算目标到自车的3D欧氏距离"""
    return np.linalg.norm(np.array(ego_translation) - np.array(obj_translation))

def quaternion_to_2d_heading(q):
    """将四元数转换为二维航向角（正北为0°，正西为90°）"""
    # 将四元数转换为欧拉角（roll, pitch, yaw），单位为弧度
    yaw_3d = q.yaw_pitch_roll[2]  # 假设四元数基于ENU坐标系（东-北-天）

    # 坐标校正：将航向角从正东为0°转换为正北为0°
    # 原欧拉角定义：0°指向东，逆时针增加
    # 目标定义：0°指向北，逆时针增加（正西为90°）
    heading = (yaw_3d + math.pi / 2) % (2 * math.pi)
    return heading


def is_in_view(ego_position, ego_rotation, obj_position, fov=110):
    """判断目标是否在自车视角范围内"""

    # 将四元数转换为偏航角（yaw，弧度）

    ego_quaternion = Quaternion(ego_rotation)
    yaw_rad = quaternion_to_2d_heading(ego_quaternion)


    # 计算目标相对自车的方向向量
    dx = obj_position[0] - ego_position[0]
    dy = obj_position[1] - ego_position[1]

    # 计算目标方位角（弧度）
    target_angle_rad = (math.atan2(dy, dx) - math.pi/2) % (2 * math.pi)

    # 计算角度差并规范化到[-π, π]
    angle_diff_rad = (target_angle_rad - yaw_rad + math.pi) % (2 * math.pi) - math.pi
    angle_diff_deg = math.degrees(abs(angle_diff_rad))


    return angle_diff_deg <= (fov / 2)



def main():
    # 示例图片文件名
    #image_file = 'n008-2018-08-01-15-16-36-0400__CAM_BACK__1533151603537558.jpg'
    #image_file = 'n008-2018-08-30-15-16-55-0400__CAM_FRONT__1535657113762404.jpg'
    image_file = 'n003-2018-01-02-11-48-43+0800__CAM_FRONT__1514864956220368'
    #获取ego信息
    ego_data = get_ego_from_fig(image_file)
    ego_position = ego_data['ego_position']
    ##打印结果
    print(f"自车位置 (米): {ego_data['ego_position']}")
    print(f"自车朝向 (四元数): {ego_data['ego_rotation']}")

    #获取目标信息
    object_data = get_all_object_from_fig(image_file)

    ##打印结果

    for i, obj in enumerate(object_data):
        if obj['type'] == 'vehicle.car' and is_in_view(ego_data['ego_position'], ego_data['ego_rotation'], obj['position']):
            print(f"目标 {i}:")
            print(f"  类型: {obj['type']}")
            print(f"  位置: {obj['position']}")
            print(f"  尺寸: {obj['size']} (长x宽x高)")
            print(f"  朝向: {obj['rotation']} ")
            distance_2D = calculate_2D_distance(ego_position, obj['position'])
            distance_3D = calculate_3D_distance(ego_position, obj['position'])
            print(f"到ego的平面距离: {distance_2D:.2f} 米")
            print(f"到ego的欧式距离: {distance_3D:.2f} 米")

            render_annotation(image_file, i, f"D:/Scenic-main/Scenic-2.x/annotation_output/{i}_annotation.png")

    #获取当前图片所属地图
    map_info = get_scene_location_from_fig(image_file)
    ##打印结果
    print(f"map_info:", map_info)



if __name__ == "__main__":
    main()