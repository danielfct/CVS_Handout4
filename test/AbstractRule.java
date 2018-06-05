package test;

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

abstract class AbstractRule implements Runnable {

	//@ predicate RuleInv() = true;
	
	//@ predicate pre() = RuleInv();
	//@ predicate post() = RuleInv();

	public static final int REFRESH_RATE = 30;
	
	
	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while (true)
		//@ invariant pre(); 
		{
			//@ open pre();
			int value = readSensors();
			setActuators(value);
			//Timeunit.SECONDS.sleep(REFRESH_RATE);
		}
	}
	
	public abstract int readSensors();
	//@ requires RuleInv();
	//@ ensures RuleInv();
	
	public abstract void setActuators(int value);
	//@ requires RuleInv();
	//@ ensures RuleInv();

}