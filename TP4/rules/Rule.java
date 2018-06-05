package rules;

import log.*;
import sensors.*;
import actuators.*;


//@ predicate_family Rule(Class c)(Rule r);


interface Rule extends Runnable {
	
	//@ predicate pre() = RuleInv(this.getClass())(this);
	//@ predicate post() = RuleInv(this.getClass())(this);

	/**
	 * Reads all sensors and calculates a value based on values read
	 * @return a value considering values from all sensors
	 */
	int readSensors();
	//@ requires Rule(this.getClass())(this);
	//@ ensures Rule(this.getClass())(this);
	
	/**
	 * Sets a value to a set of actuators (not necessarily all)
	 * @param value the value to set
	 */
	void setActuators(int value);
	//@ requires Rule(this.getClass())(this);
	//@ ensures Rule(this.getClass())(this);
	
}