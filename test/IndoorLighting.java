package test;


import sensors.*;
import actuators.*;

public class IndoorLighting extends AbstractRule {

/*@    
    		predicate RuleInv() = 
    			this.sensors |-> ?ss
    	    	    &*& this.actuators |-> ?as
	    	    &*&	array_slice_deep(ss, 0, ss.length, SensorP, unit, _, _) 
    	    	    &*& array_slice_deep(as, 0, as.length, ActuatorP, unit, _, _);
@*/

//		private static final float LOW = 0.10f;
//		private static final float MEDIUM = 0.50f;
//		private static final float HIGH = 0.90f;
	
		private Sensor[] sensors;
		private Actuator[] actuators;
	
		public IndoorLighting(Sensor[] sensors, Actuator[] actuators) 
		/*@ requires array_slice_deep(sensors, 0, sensors.length, SensorP, unit, _, _) 
		         &*& array_slice_deep(actuators, 0, actuators.length, ActuatorP, unit, _, _);
		@*/
		//@ ensures pre();

		{
			this.sensors = sensors;
			this.actuators = actuators;
			//@ close pre();
		}

		public int readSensors() 
		//@ requires RuleInv();
		//@ ensures RuleInv();
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
		}

		public void setActuators(int value)
		//@ requires RuleInv();
		//@ ensures RuleInv();
		{
			//Logger.log.write(name + " @ LAMP #"+i +" ON");
		}
		
}