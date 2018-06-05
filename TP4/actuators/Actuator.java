package actuators;

//@ predicate_family Actuator(Class c)(Actuator a;);

public interface Actuator {

	String getName();
	//@ requires [?f]ActuatorInv(?a);
	//@ ensures [f]ActuatorInv(a);
	
	int getMin();
	//@ requires [?f]ActuatorInv(?a);
	//@ ensures [f]ActuatorInv(a);
	
	int getMax();
	//@ requires [?f]ActuatorInv(?a);
	//@ ensures [f]ActuatorInv(a);
	
	int getValue();
	//@ requires [?f]ActuatorInv(?a);
	//@ ensures [f]ActuatorInv(a);
	
	void setValue(int value);
	//@ requires [?f]ActuatorInv(?a);
	//@ ensures [f]ActuatorInv(a);
	
}