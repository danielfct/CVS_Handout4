package rules;

import sensors.*;
import actuators.*;
import log.*;


/*@ predicate_family_instance RuleInv(RainProtecting.class)(RainProtecting r) = 
    		r.sensors |-> ?ss
    	    &*& r.actuators |-> ?as
	    &*&	array_slice_deep(ss, 0, ss.length, SensorP, unit, _, _) 
    	    &*& array_slice_deep(as, 0, as.length, ActuatorP, unit, _, _);
@*/	

//public class RainProtecting extends AbstractRule {
public class RainProtecting implements Rule {

	//@ predicate pre() = RuleInv(this.getClass())(this);
	//@ predicate post() = RuleInv(this.getClass())(this);


	private Sensor[] sensors;
	private Actuator[] actuators;

	public RainProtecting(Sensor[] sensors, Actuator[] actuators) 
	/*@ requires array_slice_deep(sensors, 0, sensors.length, SensorP, unit, _, _) &*&
			array_slice_deep(actuators, 0, actuators.length, ActuatorP, unit, _, _); 
	@*/
	//@ ensures pre();
	{
		this.sensors = sensors;
		this.actuators = actuators;
		//@ close RuleInv(this.getClass())(this);
		//@ close pre();
	}
	
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

	public int readSensors() 
	//@ requires RuleInv(this.getClass())(this);
	//@ ensures RuleInv(this.getClass())(this);
	{
			//@ open RuleInv();
			i = 0;
			while(i < n)
				//@ invariant array_slice_deep(ss, 0, ss.length, SensorInv, unit, _, _);
			{
				//@ array_slice_deep_split(ss, i, i+1);
				//@ assert array_slice_deep(ss, i, i+1, SensorInv, unit, _, _);
				//@ assert array_slice_deep(ss, i+1, ss.length, SensorInv, unit, _, _);
				//@ array_slice_deep_open(ss, i, i+1, SensorInv, unit, _, _);
				//@ assert SensorInv(s[i]);
				int v = s[0].get();
			}
			return 0;
		
		int sum = 0;
		for (int i = 0; i < sensors.length; i++) {
			int v = sensors[i].getValue();
			sum += v;
		}
		int avg = sum / sensors.length;
		
		return avg;
	}

	public void setActuators(int value) 
	//@ requires RuleInv(this.getClass())(this);
	//@ ensures RuleInv(this.getClass())(this);
	{
		for (int i = 0; i < sensors.length; i++) {
			Actuator a = actuators[i];
			Logger.log.write(a.getName() + " @ BLIMPS #" + i + " ON");
		}
	}


	
	
}
