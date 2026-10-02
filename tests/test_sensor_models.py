from satpredict.sensors import OffNadirConstrainedSensor, PushBroomSensor, sensor_from_name


def test_sensor_factory_and_basics():
    s1 = sensor_from_name("pushbroom", swath_km=3000, max_offnadir_deg=55)
    assert isinstance(s1, PushBroomSensor)
    assert s1.is_observable(distance_km=100, scan_angle_deg=40)
    assert not s1.is_observable(distance_km=100, scan_angle_deg=56)
    assert not s1.is_observable(distance_km=2000, scan_angle_deg=10)

    s2 = sensor_from_name("offnadir", swath_km=3000, max_offnadir_deg=30)
    assert isinstance(s2, OffNadirConstrainedSensor)
    assert s2.is_observable(distance_km=100, scan_angle_deg=20)
    assert not s2.is_observable(distance_km=100, scan_angle_deg=31)
