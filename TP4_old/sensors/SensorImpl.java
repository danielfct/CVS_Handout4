package sensors;

/*
	Daniel Filipe Santos Pimenta 45404
	CVS Handout 4 - Verifast Domotic System
*/

import java.util.concurrent.locks.*;


/*@
predicate_ctor Sensor_shared_state(Sensor s, int min, int max) () =
	s.value |-> ?v &*&
	min <= v &*& v <= max;

predicate SensorInv(Sensor s;) =
	s.mon |-> ?l &*&
	s.name |-> ?n &*&
	s.min |-> ?mi &*& 
	s.max |-> ?ma &*&
    	l != null &*& 
	lck(l, 1, Sensor_shared_state(s, mi, ma)) &*&
	mi <= ma;

predicate Sensor_frac(real r) = true;
@*/


//class SensorImpl implements Sensor {
class Sensor { 
	
	private final String name;
	private final int min;
	private final int max;
	private int value;
	private final ReentrantLock mon;

	Sensor(String name, int min, int max)
	//@ requires min <= max;
	//@ ensures SensorInv(this);
	{
		this.name = name;
		this.min = min;
		this.max = max;
		this.value = min;
		//@ close Sensor_shared_state(this, min, max)();
		//@ close enter_lck(1, Sensor_shared_state(this, min, max));
		mon = new ReentrantLock();
 		//@ close SensorInv(this);
	}
	
	public String getName()
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{
		return name;
	}
	
	public int getMin()
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{
		return min;
	}
	
	public int getMax() 
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{
		return max;
	}
	
	public int getValue() 
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{
		int v;
		//@ open SensorInv(this);
		mon.lock();
		//@ open Sensor_shared_state(this, min, max)();
		v = this.value;
		//@ close Sensor_shared_state(this, min, max)();
		mon.unlock();
		//@ close [f]SensorInv(this);
		return v; 
	}

	public void setValue(int value) 
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{ 
		//@ open SensorInv(this);
		mon.lock();
		//@ open Sensor_shared_state(this, min, max)();
		if (value > max)
			this.value = max;
		else if (value < min)
			this.value = min;
		else
			this.value = value;
		//@ close Sensor_shared_state(this, min, max)();
		mon.unlock();
      		//@ close [f]SensorInv(this);
	}
	
}