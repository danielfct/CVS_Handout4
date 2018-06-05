package rules;

import sensors.*;
import actuators.*;


/*@ predicate SensorP(unit u, Sensor s; unit value) = 
		s != null 
    	    &*& Sensor(s.getClass())(s)
    	    &*& value == unit;
    	    
    predicate ActuatorP(unit u, Actuator a; unit value) =
    		a != null
    	    &*& Actuator(a.getClass())(a)
    	    &*& value == unit;
    	    
    predicate_family_instance Rule(AbstractRule.class)(AbstractRule r) = true;
@*/

abstract class AbstractRule implements Runnable {
	
	//@ predicate pre() = Rule(this.getClass())(this) &*& [_]Timeunit_SECONDS(?s) &*& s != null;
	//@ predicate post() = Rule(this.getClass())(this);

	public static final int REFRESH_RATE = 30;
	
	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while (true) {
			int value = readSensors();
			setActuators(value);
			Timeunit.SECONDS.sleep(REFRESH_RATE);
		}
	}
	
	public abstract int readSensors();
	//@ requires RuleInv();
	//@ ensures RuleInv();
	
	public abstract void setActuators(int value);
	//@ requires RuleInv();
	//@ ensures RuleInv();

}