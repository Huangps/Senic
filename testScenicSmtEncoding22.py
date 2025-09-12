import src.scenic
import os
from src.scenic.core.distributions import *
from src.scenic.core.vectors import Vector
from src.scenic.core.regions import SectorRegion
import math
import subprocess



ego_visibleDistance = 100
ego_viewAngle = 135 #deg
ego_labelled_position = Vector(0, 0)
ego_labelled_heading = 0 #deg
egoVisibleRegion = SectorRegion(ego_labelled_position, ego_visibleDistance, \
                                math.radians(ego_labelled_heading), math.radians(ego_viewAngle))

scenic_script = "./examples/carla/test2.scenic"
scenario = src.scenic.scenarioFromFile(scenic_script)
ego = scenario.egoObject
objects = scenario.objects

print(ego.position)
print(ego.heading)


