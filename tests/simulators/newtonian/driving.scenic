
param render = False
param map = localPath('../../formats/opendrive/maps/CARLA/Town01.xodr')
model scenic.simulators.newtonian.driving_model

ego = Car in intersection, with behavior FollowLaneBehavior

ego = Car on ego.lane.predecessor, with behavior FollowLaneBehavior

behavior Walk():
    take SetWalkingDirectionAction(45 deg), SetWalkingSpeedAction(0.5)

Pedestrian on visible sidewalk, with speed 0.5, with behavior Walk

behavior Potpourri():
    take (SetReverseAction(True), SetThrottleAction(0.5), SetSteerAction(0.1),
          SetHandBrakeAction(False))
    take SetThrottleAction(0), SetBrakeAction(1), SetReverseAction(False)

third = Car on visible ego.road, with behavior Potpourri
require abs((apparent heading of third) - 180 deg) <= 30 deg

Object visible, with width 0.1, with length 0.1
