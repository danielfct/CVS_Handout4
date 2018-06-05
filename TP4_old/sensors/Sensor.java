package sensors;

/*
Daniel Filipe Santos Pimenta 45404
CVS Handout 4 - Verifast Domotic System
*/

import java.util.concurrent.locks.*;

/*@
predicate_ctor Sensor_shared_state(SensorImpl s, int min, int max) () =
	s.value |-> ?v &*&
	min <= v &*& v <= max;

predicate SensorInv(SensorImpl s;) =
	s.mon |-> ?l &*&
	s.name |-> ?n &*&
	s.min |-> ?mi &*& 
	s.max |-> ?ma &*&
    	l != null &*& 
	lck(l, 1, Sensor_shared_state(s, mi, ma)) &*&
	n != null &*&
	mi <= ma;
@*/

interface Sensor {
	
	/**
	 * Get the name of the sensor
	 * @return the name
	 */
 	String getName();
	//@ requires [?f]SensorInv(?s);
	//@ ensures [f]SensorInv(s);
	
	/**
	 * Get the minimum value of the sensor
	 * @return the minimum
	 */
	int getMin();
	//@ requires [?f]SensorInv(?s);
	//@ ensures [f]SensorInv(s);
	
	/**
	 * Get the maximum value of the sensor
	 * @return the maximum
	 */
	int getMax();
	//@ requires [?f]SensorInv(?s);
	//@ ensures [f]SensorInv(s);
	
	/**
	 * Get the value of the sensor
	 * @return the value
	 */
	int getValue();
	//@ requires [?f]SensorInv(?s);
	//@ ensures [f]SensorInv(s);

	/**
	 * Set the value of the sensor
	 * @param value new value of this sensor
	 */
	void setValue(int value);
	//@ requires [?f]SensorInv(?s);
	//@ ensures [f]SensorInv(s);
	
}