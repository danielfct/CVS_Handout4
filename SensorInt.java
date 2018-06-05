/*
	Daniel Filipe Santos Pimenta 45404
	CVS Handout 3 - Verifast concurrency with monitors and shared resources
*/

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
predicate_ctor SensorInt_shared_state(SensorInt s, int min, int max) () =
	s.value |-> ?v &*&
	min <= v &*& v <= max;

predicate SensorIntInv(SensorInt s;) =
	s.mon |-> ?l &*&
	s.min |-> ?n &*& 
	s.max |-> ?m &*&
    	l != null &*& 
	lck(l, 1, SensorInt_shared_state(s, n, m)) &*&
	n <= m;
@*/

class SensorInt {
	
	private int value;
	private final int min;
	private final int max;
	private final Thread th;
	private final ReentrantLock mon;

	SensorInt(int min, int max)
	//@ requires min <= max &*& [_]System_out(?o) &*& o != null &*& [_]TimeUnit_SECONDS(?ts) &*& ts != null;
	//@ ensures [1/2]SensorIntInv(this);
	{
		this.min = min;
		this.max = max;
		this.value = min;
		//@ close SensorInt_shared_state(this, min, max)();
		//@ close enter_lck(1, SensorInt_shared_state(this, min, max));
		mon = new ReentrantLock();
 		//@ close SensorIntInv(this);
 		//@ close SensorInt_frac(1/2);
		this.th = new Thread(new Probe(this));
		this.th.start();
	}
	
	int getValue() 
	//@ requires [?f]SensorIntInv(this);
	//@ ensures [f]SensorIntInv(this);
	{
		int v;
		//@ open SensorIntInv(this);
		mon.lock();
		//@ open SensorInt_shared_state(this, min, max)();
		v = this.value;
		//@ close SensorInt_shared_state(this, min, max)();
		mon.unlock();
		//@ close [f]SensorIntInv(this);
		return v; 
	}

	void set(int value) 
	//@ requires [?f]SensorIntInv(this);
	//@ ensures [f]SensorIntInv(this);
	{ 
		//@ open SensorIntInv(this);
		mon.lock();
		//@ open SensorInt_shared_state(this, min, max)();
		if (value > max)
			this.value = max;
		else if (value < min)
			this.value = min;
		else
			this.value = value;
		//@ close SensorInt_shared_state(this, min, max)();
		mon.unlock();
      		//@ close [f]SensorIntInv(this);
	}
	
	int getMax() 
	//@ requires [?f]SensorIntInv(this);
	//@ ensures [f]SensorIntInv(this);
	{
		return max;
	}
	
	int getMin()
	//@ requires [?f]SensorIntInv(this);
	//@ ensures [f]SensorIntInv(this);
	{
		return min;
	}
	
	public static void main(String args[]) throws InterruptedException //@ ensures true;
	//@ requires [_]System_out(?o) &*& o != null &*& [_]TimeUnit_SECONDS(?ts) &*& ts != null;
	//@ ensures true;
	{
		SensorInt s = new SensorInt(0, 10);
		//@ assert [?f]SensorIntInv(s);
       
       		//@ close SensorInt_frac(f);
		while (true) 
		/*@ invariant SensorInt_frac(f) &*& [f]SensorIntInv(s) &*&
			[_]System_out(o) &*& o != null &*&
			[_]TimeUnit_SECONDS(ts) &*& ts != null;
		@*/
		{
			// get and print a sample every 5 seconds
			int v = s.getValue();
			System.out.println("SensorInt: " + Integer.toString(v));
			TimeUnit.SECONDS.sleep(5);
		}
	}
}