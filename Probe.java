/*
	Daniel Filipe Santos Pimenta 45404
	CVS Handout 3 - Verifast concurrency with monitors and shared resources
*/

import java.util.concurrent.*;
import java.util.Random;

/*@ 
predicate SensorInt_frac(real r) = true;

predicate ProbeInv(Probe p;) = 
	p.sensor |-> ?s &*& 
	s != null &*& 
	[_]SensorIntInv(s);
@*/
class Probe implements Runnable {

	//@ predicate pre() = ProbeInv(this) &*& [_]System_out(?o) &*& o != null &*& [_]TimeUnit_SECONDS(?ts) &*& ts != null;
	//@ predicate post() = ProbeInv(this);

	private SensorInt sensor;
	
	public Probe(SensorInt sensor) 
	/*@ requires sensor != null 
		&*& SensorInt_frac(?f) 
		&*& [f]SensorIntInv(sensor) 
		&*& [_]System_out(?o) &*& o != null &*& [_]TimeUnit_SECONDS(?ts) &*& ts != null;
	@*/
	//@ ensures pre();
	{
		this.sensor = sensor;
		//@ close pre();
	}
	
	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		Random r = new Random();
		int min = sensor.getMin();
		int max = sensor.getMax();
		while (true) 
		//@ invariant pre();
		{
			// produce a new value every 2 seconds
			int v = r.nextInt(max - min + 1) + min;  // random between (inclusive) min and max
			System.out.println("Probe: " + Integer.toString(v));
			sensor.set(v);
			try {
				TimeUnit.SECONDS.sleep(2);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}
}