package actuators;

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
predicate_ctor Actuator_shared_state(ActuatorImpl a, int min, int max) () =
	a.value |-> ?v &*&
	min <= v &*& v <= max;

predicate_family_instance Actuator(ActuatorImpl.class)(ActuatorImpl a) =
	a.mon |-> ?l &*&
	a.name |-> ?n &*&
	a.min |-> ?mi &*& 
	a.max |-> ?ma &*&
    l != null &*& 
	lck(l, 1, Actuator_shared_state(a, mi, ma)) &*&
	mi <= ma;
@*/

class ActuatorImpl implements Actuator {
	
	private final String name;
	private final int min;
	private final int max;
	private int value;
	private final ReentrantLock mon;

	ActuatorImpl(String name, int min, int max)
	//@ requires min <= max;
	//@ ensures ActuatorInv(this);
	{
		this.name = name;
		this.min = min;
		this.max = max;
		this.value = min;
		//@ close Actuator_shared_state(this, min, max)();
		//@ close enter_lck(1, Actuator_shared_state(this, min, max));
		mon = new ReentrantLock();
 		//@ close ActuatorInv(this);
	}
	
	public String getName()
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{
		return name;
	}
	
	public int getMin()
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{
		return min;
	}
	
	public int getMax() 
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{
		return max;
	}
	
	public int getValue() 
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{
		int v;
		//@ open ActuatorInv(this);
		mon.lock();
		//@ open Actuator_shared_state(this, min, max)();
		v = this.value;
		//@ close Actuator_shared_state(this, min, max)();
		mon.unlock();
		//@ close [f]ActuatorInv(this);
		return v; 
	}

	public void setValue(int value) 
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{ 
		//@ open ActuatorInv(this);
		mon.lock();
		//@ open Actuator_shared_state(this, min, max)();
		if (value > max)
			this.value = max;
		else if (value < min)
			this.value = min;
		else
			this.value = value;
		//@ close Actuator_shared_state(this, min, max)();
		mon.unlock();
      	//@ close [f]ActuatorInv(this);
	}
	
}
