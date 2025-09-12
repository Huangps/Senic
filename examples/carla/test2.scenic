
model scenic.domains.driving.model


curbRegion1 = Uniform(*network.curbRegion)

intersection = Uniform(*network.intersections)
lane = Uniform(*network.lanes)
curb =  Uniform(*network.curbRegion)


ego = Car on lane, facing roadDirection  #(313.46979041968507, 666.6358689893677)
#ca1 = Car on ego.oppositeLaneGroup ,facing Range(-15,15) deg relative to ego.heading+3.14
human = Pedestrian on visible lane

#require  ego can see ca1

