
from src.scenic.domains.driving.roads import NetworkElement, ManeuverType, Network, Road, Lane, LaneSection, Intersection

from nuscenes.map_expansion.map_api import NuScenesMap

network = Network.fromPickle('D:/Scenic-main/Scenic-scenic-query/src/scenic/domains/driving/boston-network.pickle')
dataroot = 'D:/Scenic-main/nuscenesData/dataset'
map_api = NuScenesMap(dataroot=dataroot, map_name='boston-seaport')

from src.scenic.core.vectors import Vector


point1 = Vector(1184, 126)
point2 = Vector(1870, 1309)

#
point3 = Vector(313.4697, 666.6358)  # 预期为intersection 实际为intersection
point4 = Vector(350, 750)   # 预期为road   实际为road
point5 = Vector(1497, 1362)   # 预期为intersection 实际为intersection

# 根据nuscenes介绍，lane属于road的一部分，
# lanes为相同方向的道路， 例如假设lanes.rightLine 和lanes.leftLine存在，那么他们的通行方向是一致的
point6 = Vector(1495.35, 1356.37)   # 预期为lane    实际为road
point7 = Vector(2710.5, 1038.37)   # 预期为lane    实际为road


point8 = Vector(2706, 1089) # 预期为intersection 实际为intersection
point9 = Vector(2710, 1095) # 预期为road 实际为road
point10 = Vector(2709, 1083) # 预期为road 实际为road
point11 = Vector(2700, 1085) # 预期为intersection 实际为intersection
point12 = Vector(495.241, 1697.111)
point13 = Vector(480.038,  1716.852)
element = network.elementAt(point12)
#a=element.orientation



#element.from_edge_line_token
if element:
    print(f"Network element: {element} (type: {type(element).__name__})")

print(len(network.roads))
print(len(network.lanes))
print(len(network.intersections))