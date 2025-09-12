import pytest

from tests.utils import compileScenic, pickle_test, sampleScene, tryPickling

# Suppress potential warning about missing the carla package
pytestmark = pytest.mark.filterwarnings("ignore::scenic.core.simulators.SimulatorInterfaceWarning")

def test_basic(loadLocalScenario):
    scenario = loadLocalScenario('basic.scenic')
    scenario.generate(maxIterations=1000)


def test_simulator_import():
    pytest.importorskip("carla")
    from scenic.simulators.carla import CarlaSimulator


def test_consistent_object_type():
    pytest.importorskip("carla")
    code = f"""
        param map = 'tests/formats/opendrive/maps/CARLA/Town01.xodr'
        param carla_map = 'Town01'
        model scenic.simulators.carla.model
        action = SetGearAction(0)
        ego = Car
        assert action.canBeTakenBy(ego)
    """
    for _ in range(2):
        compileScenic(code)


@pickle_test
@pytest.mark.slow
def test_pickle(loadLocalScenario):
    scenario = tryPickling(loadLocalScenario('basic.scenic'))
    tryPickling(sampleScene(scenario, maxIterations=1000))
