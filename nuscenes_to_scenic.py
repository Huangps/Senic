import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from scenic.core.vectors import Vector
#from scenic.core.geometry import Polygon, Polyline
from scenic.core.regions import PolygonalRegion, PolylineRegion
from nuscenes.map_expansion.map_api import NuScenesMap
from shapely.geometry import LineString, Polygon as ShapelyPolygon


@dataclass
class NetworkElement:
    """Base class for network elements."""
    uid: str
    polygon: PolygonalRegion
    centerline: Optional[PolylineRegion] = None


@dataclass
class Lane(NetworkElement):
    """Represents a lane in the road network."""
    road: Optional['Road'] = None
    successors: List['Lane'] = None
    predecessors: List['Lane'] = None


@dataclass
class Road(NetworkElement):
    """Represents a road containing multiple lanes."""
    lanes: List[Lane] = None
    successors: List['Road'] = None
    predecessors: List['Road'] = None


@dataclass
class Intersection(NetworkElement):
    """Represents an intersection."""
    incoming_roads: List[Road] = None
    outgoing_roads: List[Road] = None


class ScenicNetwork:
    """Container for the complete road network."""

    def __init__(self):
        self.roads: Dict[str, Road] = {}
        self.lanes: Dict[str, Lane] = {}
        self.intersections: Dict[str, Intersection] = {}

    def add_road(self, road: Road):
        self.roads[road.uid] = road

    def add_lane(self, lane: Lane):
        self.lanes[lane.uid] = lane

    def add_intersection(self, intersection: Intersection):
        self.intersections[intersection.uid] = intersection


def convert_nuscenes_to_scenic(nusc_map: NuScenesMap, map_name: str) -> ScenicNetwork:
    """
    Convert a nuScenes map to a Scenic network.

    Args:
        nusc_map: Loaded nuScenes map API object
        map_name: Name of the map (e.g., 'singapore-onenorth')

    Returns:
        ScenicNetwork object containing the converted map
    """
    network = ScenicNetwork()

    # 1. Process all lanes first
    lane_records = nusc_map.get_records_in_patch(
        nusc_map.extent,
        layer_names=['lane'],
        mode='intersect'
    )

    # First pass: create all lane objects
    for lane_token in lane_records['lane']:
        lane_record = nusc_map.get('lane', lane_token)

        # Get geometry
        polygon = nusc_map.extract_polygon(lane_token)
        line = nusc_map.get('lane', lane_token)['line']

        # Convert to Scenic types
        scenic_polygon = PolygonalRegion(polygon=[Vector(*point) for point in polygon.exterior.coords])
        scenic_centerline = PolylineRegion(polyline=[Vector(*point) for point in line])

        # Create lane
        lane = Lane(
            uid=lane_token,
            polygon=scenic_polygon,
            centerline=scenic_centerline,
            successors=[],
            predecessors=[]
        )
        network.add_lane(lane)

    # Second pass: establish connections between lanes
    for lane_token in network.lanes:
        lane_record = nusc_map.get('lane', lane_token)

        # Connect successors
        for succ_token in lane_record['successor']:
            if succ_token in network.lanes:
                network.lanes[lane_token].successors.append(network.lanes[succ_token])

        # Connect predecessors
        for pred_token in lane_record['predecessor']:
            if pred_token in network.lanes:
                network.lanes[lane_token].predecessors.append(network.lanes[pred_token])

    # 2. Process roads (group of lanes)
    road_records = nusc_map.get_records_in_patch(
        nusc_map.extent,
        layer_names=['road_segment'],
        mode='intersect'
    )

    for road_token in road_records['road_segment']:
        road_record = nusc_map.get('road_segment', road_token)

        # Find lanes belonging to this road
        road_lanes = [
            lane for lane in network.lanes.values()
            if nusc_map.get('lane', lane.uid)['road_segment'] == road_token
        ]

        if not road_lanes:
            continue

        # Create polygon covering all lanes
        polygons = [lane.polygon.polygons for lane in road_lanes]
        combined_poly = ShapelyPolygon()
        for poly in polygons:
            combined_poly = combined_poly.union(ShapelyPolygon(poly))

        scenic_polygon = PolygonalRegion(polygon=[Vector(*point) for point in combined_poly.exterior.coords])

        # Create road
        road = Road(
            uid=road_token,
            polygon=scenic_polygon,
            lanes=road_lanes,
            successors=[],
            predecessors=[]
        )

        # Set back-reference in lanes
        for lane in road_lanes:
            lane.road = road

        network.add_road(road)

    # 3. Process intersections
    area_records = nusc_map.get_records_in_patch(
        nusc_map.extent,
        layer_names=['area'],
        mode='intersect'
    )

    for area_token in area_records['area']:
        area_record = nusc_map.get('area', area_token)

        if not area_record['is_intersection']:
            continue

        # Get intersection polygon
        polygon = nusc_map.extract_polygon(area_token)
        scenic_polygon = PolygonalRegion(polygon=[Vector(*point) for point in polygon.exterior.coords])

        # Find incoming/outgoing roads
        incoming = []
        outgoing = []

        # Create intersection
        intersection = Intersection(
            uid=area_token,
            polygon=scenic_polygon,
            incoming_roads=incoming,
            outgoing_roads=outgoing
        )
        network.add_intersection(intersection)

    return network


# Example usage
if __name__ == "__main__":
    # Initialize nuScenes map (replace with your actual path)
    nusc_map = NuScenesMap(dataroot='D:/Scenic-main/nuscenesData/dataset/', map_name='singapore-onenorth')

    # Convert to Scenic network
    scenic_network = convert_nuscenes_to_scenic(nusc_map, 'singapore-onenorth')

    # Print summary
    print(f"Converted network contains:")
    print(f"- {len(scenic_network.roads)} roads")
    print(f"- {len(scenic_network.lanes)} lanes")
    print(f"- {len(scenic_network.intersections)} intersections")