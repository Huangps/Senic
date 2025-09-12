
model scenic.domains.driving.model


curbRegion1 = Uniform(*network.curbRegion)

intersection = Uniform(*network.intersections)
lane = Uniform(*network.lanes)

lanesWithRightLane = filter(lambda i: i._laneToLeft, network.laneSections)

#egoLane = Uniform(*lanesWithRightLane)

ego = Car on lane.centerline

point1 = OrientedPoint at ego offset  by (5,0), facing ego.heading
point2 = OrientedPoint at point1 offset  by (-10,0)

car1 =  Car at point1, facing ego.heading
car2 =  Car at point2, facing ego.heading




