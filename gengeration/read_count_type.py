import json
import math
from typing import Dict, List
from collections import defaultdict
from pyquaternion import Quaternion
from Heading_rad import quaternion_to_2d_heading
from readLable import (
    get_ego_from_fig,
    get_all_object_from_fig,
    get_scene_location_from_fig,
    calculate_2D_distance,
    calculate_3D_distance,
    is_in_view
)


def filter_objects_in_view_and_distance(filename: str, max_distance: float = 50.0) -> List[dict]:
    """
    Filter objects that are:
    1. Within field of view
    2. Within max_distance
    3. Of type 'vehicle' or 'human'
    Returns filtered list of objects with complete information
    """
    try:
        ego_data = get_ego_from_fig(filename)
        objects = get_all_object_from_fig(filename)

        filtered_objects = [
            obj for obj in objects
            if (is_in_view(ego_data['ego_position'],
                           ego_data['ego_rotation'],
                           obj['position']) and
                calculate_2D_distance(ego_data['ego_position'], obj['position']) <= max_distance and
                ('vehicle' in obj['type'] or 'human' in obj['type']))
        ]

        # Add distance information to each object
        for obj in filtered_objects:
            obj['distance_2d'] = calculate_2D_distance(ego_data['ego_position'], obj['position'])
            obj['distance_3d'] = calculate_3D_distance(ego_data['ego_position'], obj['position'])

        return filtered_objects, ego_data  # 返回ego_data

    except Exception as e:
        print(f"Error filtering objects: {str(e)}")
        return [], None


def convert_orientations_to_angle(filtered_objects: List[dict]) -> List[dict]:
    """Convert orientation quaternions to radians for all filtered objects"""
    for obj in filtered_objects:
        q = Quaternion(obj['rotation'])
        obj['orientation_rad'] = quaternion_to_2d_heading(q)
    return filtered_objects


def count_objects_by_type(filtered_objects: List[dict]) -> Dict[str, int]:
    """
    Count objects by their base type
    Returns dictionary {type: count}
    """
    type_counts = defaultdict(int)
    for obj in filtered_objects:
        base_type = obj['type'].split('.')[0]
        type_counts[base_type] += 1
    return dict(type_counts)


def print_ego_info(ego_data: dict):
    """Print detailed ego vehicle information"""
    if ego_data is None:
        return

    print("\n=== Ego Vehicle Information ===")
    print(f"Position: {ego_data['ego_position']}")
    q = Quaternion(ego_data['ego_rotation'])
    heading_rad = quaternion_to_2d_heading(q)
    print(f"Rotation (quaternion): {ego_data['ego_rotation']}")
    print(f"Heading (rad): {heading_rad:.3f}")
    if 'velocity' in ego_data:
        print(f"Velocity: {ego_data['velocity']}")
    if 'acceleration' in ego_data:
        print(f"Acceleration: {ego_data['acceleration']}")


def print_detailed_objects(filtered_objects: List[dict]):
    """
    Print detailed information for filtered objects with orientation in radians
    """
    print("\n=== Filtered Objects Details ===")
    for i, obj in enumerate(filtered_objects, 1):
        print(f"\nObject {i}:")
        print(f"  Type: {obj['type']}")
        print(f"  Position: {obj['position']}")
        # print(f"  Dimensions: {obj['size']}")
        print(f"  Orientation (rad): {obj['orientation_rad']:.3f}")
        print(f"  Distance: 2D={obj['distance_2d']:.1f}m, 3D={obj['distance_3d']:.1f}m")


def save_detailed_objects_to_json(filtered_objects: List[dict], ego_data: dict, output_path: str):
    """
    Save filtered objects' detailed information and ego data to JSON file
    """
    output_data = {
        'ego': ego_data,
        'objects': filtered_objects,
        'summary': {
            'total_count': len(filtered_objects),
            'type_counts': count_objects_by_type(filtered_objects)
        }
    }

    with open(output_path, 'w') as f:
        json.dump(output_data, f, indent=2, ensure_ascii=False)
    print(f"Detailed object information saved to {output_path}")


if __name__ == "__main__":
    # Example usage
    image_file = 'n008-2018-08-01-15-16-36-0400__CAM_FRONT__1533151591862404'

    # Step 1: Filter objects (in view, within 50m, and of type vehicle/human)
    filtered_objects, ego_data = filter_objects_in_view_and_distance(image_file)

    # Step 2: Convert orientations to radians
    filtered_objects = convert_orientations_to_angle(filtered_objects)

    # Step 3: Print statistics
    counts = count_objects_by_type(filtered_objects)
    print("Object counts (in view, within 50m, type vehicle/human):")
    for obj_type, num in counts.items():
        print(f"{obj_type}: {num}")

    # Step 4: Print ego vehicle information
    print_ego_info(ego_data)

    # Step 5: Print detailed information for each object
    print_detailed_objects(filtered_objects)

    # Step 6: Save detailed information to JSON
    save_detailed_objects_to_json(filtered_objects, ego_data, "filtered_objects_details.json")