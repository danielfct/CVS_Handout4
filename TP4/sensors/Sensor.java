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

predicate_family Sensor(Class c)(Sensor s;);
@*/

interface Sensor {
	
	/**
	 * Get the name of the sensor
	 * @return the name
	 */
 	String getName();
	//@ requires Sensor(this.getClass())(this);
	//@ ensures Sensor(this.getClass())(this);
	
	/**
	 * Get the minimum value of the sensor
	 * @return the minimum
	 */
	int getMin();
	//@ requires Sensor(this.getClass())(this);
	//@ ensures Sensor(this.getClass())(this);
	
	/**
	 * Get the maximum value of the sensor
	 * @return the maximum
	 */
	int getMax();
	//@ requires Sensor(this.getClass())(this);
	//@ ensures Sensor(this.getClass())(this);
	
	/**
	 * Get the value of the sensor
	 * @return the value
	 */
	int getValue();
	//@ requires Sensor(this.getClass())(this);
	//@ ensures Sensor(this.getClass())(this);

	/**
	 * Set the value of the sensor
	 * @param value new value of this sensor
	 */
	void setValue(int value);
	//@ requires Sensor(this.getClass())(this);
	//@ ensures Sensor(this.getClass())(this);
	
}