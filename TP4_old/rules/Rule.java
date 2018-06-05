package rules;

import sensors.*;
import actuators.*;

	/*@ predicate SensorP(unit u, Sensor s; unit value) = 
			s != null 
    	    &*& SensorInv(s)
    	    &*& value == unit;
    	    
    predicate ActuatorP(unit u, Actuator a; unit value) =
    		a != null
    	    &*& ActuatorInv(a)
    	    &*& value == unit;
	@*/

//@ predicate_family RuleInv(Class c)(Rule r;);


interface Rule extends Runnable {
	
	//@ predicate pre() = RuleInv(this.getClass())(this);
	//@ predicate post() = RuleInv(this.getClass())(this);

	/**
	 * Reads all sensors and calculates a value based on values read
	 * @return a value considering values from all sensors
	 */
	int readSensors();
	//@ requires RuleInv(this.getClass())(this);
	//@ ensures RuleInv(this.getClass())(this);
	
	/**
	 * Sets a value to a set of actuators (not necessarily all)
	 * @param value the value to set
	 */
	void setActuators(int value);
	//@ requires RuleInv(this.getClass())(this);
	//@ ensures RuleInv(this.getClass())(this);
	
}