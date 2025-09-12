
from src.scenic.domains.driving.roads import NetworkElement, ManeuverType, Network, Road, Lane, LaneSection, Intersection

from nuscenes.map_expansion.map_api import NuScenesMap

network = Network.fromPickle('D:/Scenic-main/Scenic-scenic-query/src/scenic/domains/driving/boston-network.pickle')
dataroot = 'D:/Scenic-main/nuscenesData/dataset'
map_api = NuScenesMap(dataroot=dataroot, map_name='boston-seaport')

from src.scenic.core.vectors import Vector
from src.scenic.core.regions import CircularRegion

ego_visibleDistance = 100


smt_file = "road_constraints.smt2"
cached_variables = {
    'variables': [],       # 存储所有生成的变量名（如 ['x!0', 'y!0']）
    'regions': {},          # 存储区域对象到变量名的映射
    'regionAroundEgo': None, # 可选：特殊键，但建议使用 'regions' 统一管理
    'regionAroundEgo_polygon': None
}
label_ego_pos = Vector(350, 750)
regionAroundEgo = CircularRegion(label_ego_pos, ego_visibleDistance)

cached_variables['regionAroundEgo'] = regionAroundEgo
cached_variables['regionAroundEgo_polygon'] = regionAroundEgo.polygon


roadRegion = network.roadRegion
roadSMT = roadRegion.encodeToSMT(smt_file, cached_variables, debug=True)



