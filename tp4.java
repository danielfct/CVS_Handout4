import java.util.concurrent.*;
import java.util.concurrent.locks.*;
import java.io.*;
import java.util.*;

class Probe implements Runnable {

	/*@ 
	predicate ProbeInv() = 
		this.sensor |-> ?s 
		&*& s != null 
		&*& [_]s.SensorInv();
		
	predicate pre() = 
		ProbeInv() 
		&*& [_]System_out(?o) 
		&*& o != null 
		&*& [_]TimeUnit_SECONDS(?ts) 
		&*& ts != null;
		
	predicate post() = 
		ProbeInv();
	@*/ 
	
	private Sensor sensor;
	
	public Probe(Sensor sensor) 
	/*@ requires sensor != null 
		&*& Sensor_frac(?f) 
		&*& sensor.SensorInv() 
		&*& [_]System_out(?o) 
		&*& o != null 
		&*& [_]TimeUnit_SECONDS(?ts) 
		&*& ts != null;
	@*/
	//@ ensures pre();
	{
		this.sensor = sensor;
		//@ close ProbeInv();
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
			sensor.setValue(v);
			try {
				TimeUnit.SECONDS.sleep(2);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}
}

/*@
predicate_ctor Sensor_shared_state(SensorImpl s, int min, int max) () =
	s.value |-> ?v &*&
	min <= v &*& v <= max;

predicate Sensor_frac(real r) = true;
@*/

interface Sensor {
	
	//@ predicate SensorInv();
	
 	String getName();
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	
	int getMin();
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();

	int getMax();
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();

	int getValue();
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();

	void setValue(int value);
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	
}

public class SensorImpl implements Sensor {
	
	/*@
	predicate SensorInv() =
		this.mon |-> ?l &*&
		this.name |-> ?n &*&
		this.min |-> ?mi &*& 
		this.max |-> ?ma &*&
    		l != null &*& 
		lck(l, 1, Sensor_shared_state(this, mi, ma)) &*&
		mi <= ma;
	@*/
	
	private final String name;
	private final int min;
	private final int max;
	private int value;
	private final ReentrantLock mon;

	SensorImpl(String name, int min, int max)
	//@ requires min <= max &*& Sensor_frac(?f);
	//@ ensures Sensor_frac(f) &*& SensorInv();
	{
		this.name = name;
		this.min = min;
		this.max = max;
		this.value = min;
		//@ close Sensor_shared_state(this, min, max)();
		//@ close enter_lck(1, Sensor_shared_state(this, min, max));
		mon = new ReentrantLock();
 		//@ close SensorInv();
	}
	
	public String getName()
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	{
		return name;
	}
	
	public int getMin()
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	{
		return min;
	}
	
	public int getMax() 
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	{
		return max;
	}
	
	public int getValue() 
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	{
		int v;
		//@ open SensorInv();
		mon.lock();
		//@ open Sensor_shared_state(this, min, max)();
		v = this.value;
		//@ close Sensor_shared_state(this, min, max)();
		mon.unlock();
		//@ close [f]SensorInv();
		return v; 
	}

	public void setValue(int value) 
	//@ requires [?f]SensorInv();
	//@ ensures [f]SensorInv();
	{ 
		//@ open SensorInv();
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
      		//@ close [f]SensorInv();
	}
	
}

/*@
predicate_ctor Actuator_shared_state(ActuatorImpl a, int min, int max) () =
	a.value |-> ?v 
	&*& min <= v 
	&*& v <= max;

predicate Actuator_frac(real r) = true;
@*/

public interface Actuator {

	//@ predicate ActuatorInv();

	String getName();
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	
	int getMin();
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	
	int getMax();
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	
	int getValue();
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	
	void setValue(int value);
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();	
}


class ActuatorImpl implements Actuator {

	/*@
	predicate ActuatorInv() =
		this.mon |-> ?l 
		&*& this.name |-> ?n 
		&*& this.min |-> ?mi 
		&*& this.max |-> ?ma 
		&*& l != null 
		&*& lck(l, 1, Actuator_shared_state(this, mi, ma)) 
		&*& mi <= ma;
	@*/
	
	private final String name;
	private final int min;
	private final int max;
	private int value;
	private final ReentrantLock mon;

	ActuatorImpl(String name, int min, int max)
	//@ requires min <= max &*& Actuator_frac(?f);
	//@ ensures Actuator_frac(f) &*& ActuatorInv();
	{
		this.name = name;
		this.min = min;
		this.max = max;
		this.value = min;
		//@ close Actuator_shared_state(this, min, max)();
		//@ close enter_lck(1, Actuator_shared_state(this, min, max));
		mon = new ReentrantLock();
 		//@ close ActuatorInv();
	}
	
	public String getName()
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	{
		return name;
	}
	
	public int getMin()
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	{
		return min;
	}
	
	public int getMax() 
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	{
		return max;
	}
	
	public int getValue() 
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	{
		int v;
		//@ open ActuatorInv();
		mon.lock();
		//@ open Actuator_shared_state(this, min, max)();
		v = this.value;
		//@ close Actuator_shared_state(this, min, max)();
		mon.unlock();
		//@ close [f]ActuatorInv();
		return v; 
	}

	public void setValue(int value) 
	//@ requires [?f]ActuatorInv();
	//@ ensures [f]ActuatorInv();
	{ 
		//@ open ActuatorInv();
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
      		//@ close [f]ActuatorInv();
	}
	
}

interface Log {
	
	//@ predicate LogInv();

	void write(String message);
	//@ requires LogInv();
	//@ ensures LogInv();

	String[] read(int fromIndex);
	//@ requires LogInv();
	//@ ensures LogInv();

	int size();
	//@ requires LogInv();
	//@ ensures LogInv();
}
 	
public final class Logger {

	/*@
	predicate LogInv() =
		this.messages |-> ?m
		&*& m != null;
	@*/

	private static final int INIT_SIZE = 32;
	
	public static final Logger log;
	
	private String[] messages;
	
	public Logger()
	//@ requires emp;
	//@ ensures LogInv();
	{ 
	 	messages = new String[INIT_SIZE];
        	//@ close LogInv();
	}

	
	public static Logger getLog()
	//@ requires Logger_log(?l) &*& (l == null ? true : l.LogInv());
	//@ ensures Logger_log(result) &*& result.LogInv(); 
	{
		if (log == null) { 
			log = new Logger(); 
		}
		return log;
	}
	
	public void write(String message)
	//@ requires LogInv();
        //@ ensures LogInv();
	{

	}

	public String[] read(int fromIndex) 
	//@ requires [?f]LogInv();
        //@ ensures [f]LogInv() &*& result != null &*& array_slice(result, 0, result.length, _);
	{
		return new String[0];
	
	}

	public int size() 
	//@ requires [?f]LogInv();
        //@ ensures [f]LogInv() &*& result >= 0;
	{
		//return messages.size();
		return 0;
	}

}

/*@
predicate SensorP(unit u, Sensor s; unit value) = 
	s != null 
	&*& s.SensorInv()
	&*& value == unit;
    	    
predicate ActuatorP(unit u, Actuator a; unit value) =
	a != null
	&*& a.ActuatorInv()
	&*& value == unit;
@*/


interface Rule extends Runnable {

    	//@ predicate RuleInv();

	int readSensors();
	//@ requires RuleInv();
	//@ ensures RuleInv();
	
	void setActuators(int value);
	//@ requires RuleInv();
	//@ ensures RuleInv();
	
}


abstract class AbstractRule implements Rule {
    	
	public static final int REFRESH_RATE = 30;

	public abstract void run();
	//@ requires pre();
	//@ ensures post();
	
	public abstract int readSensors();
	//@ requires RuleInv();
	//@ ensures RuleInv();
	
	public abstract void setActuators(int value);
	//@ requires RuleInv();
	//@ ensures RuleInv();

}


public final class IndoorLighting extends AbstractRule {

	/*@ 
	predicate RuleInv() = 
    		this.sensors |-> ?s
    	    	&*& this.actuators |-> ?a
	    	&*& array_slice_deep(s, 0, s.length, SensorP, unit, _, _) 
    	    	&*& array_slice_deep(a, 0, a.length, ActuatorP, unit, _, _);
	@*/

	//@ predicate pre() = RuleInv() &*& [_]TimeUnit_SECONDS(?s) &*& s != null;
	//@ predicate post() = RuleInv() &*& [_]TimeUnit_SECONDS(?s) &*& s != null;


	private static final real LOW = 0.10;
	private static final real MEDIUM = 0.50;
	private static final real HIGH = 0.90;

	Sensor[] sensors;
	Actuator[] actuators;
	
	public IndoorLighting(Sensor[] sensors, Actuator[] actuators) 
	/*@ requires array_slice_deep(sensors, 0, sensors.length, SensorP, unit, _, _) 
		&*& array_slice_deep(actuators, 0, actuators.length, ActuatorP, unit, _, _)
		&*& [_]TimeUnit_SECONDS(?s) &*& s != null;
	@*/
	//@ ensures pre();
	{
		this.sensors = sensors;
		this.actuators = actuators;
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
			TimeUnit.SECONDS.sleep(REFRESH_RATE);
		}
	}
		
	public int readSensors()
	//@ requires RuleInv();
	//@ ensures RuleInv();
	{
		//@ open RuleInv();
		1;
		int i = 0;
		while(i < sensors.length)
		//@ invariant sensors |-> ?ss &*& array_slice_deep(ss, i, ss.length, SensorP, unit, _, _);
		{
			//@ array_slice_deep_split(ss, i, i+1);
			//@ array_slice_deep_open(ss, i);
			//@ open SensorP(unit, ss[i], _);
			int v = sensors[i].getValue();
		}
		return 0;
	}

	public void setActuators(int value) 
	//@ requires RuleInv();
	//@ ensures RuleInv();
	{
		for (int i = 0; i < actuators.length; i++)
		/*@ invariant actuators |-> ?as 
			&*& array_slice_deep(as, 0, as.length, ActuatorP, unit, _, _) 
			&*& 0 <= i 
			&*& i <= as.length;
		@*/
		{
			//@ array_slice_deep_split(as, 0, i);
			//@ array_slice_deep_split(as, i, i+1);
			//@ array_slice_deep_open(as, i);
			//@ open ActuatorP(unit, as[i], _);
			Actuator a = actuators[i];
			//Logger.log.write(a.getName() + " @ BLIMPS #" + Integer.toString(i) + " ON");
			//@ close ActuatorP(unit, as[i], _);
			//@ array_slice_deep_close(as, i, ActuatorP, unit);
			//@ array_slice_deep_join(as, 0);
			//@ array_slice_deep_join(as, 0);
		}
	}
		
}	


public final class RainProtecting extends AbstractRule {

	/*@ 
	predicate RuleInv() = 
    		this.sensors |-> ?s
    	    	&*& this.actuators |-> ?a
	    	&*& array_slice_deep(s, 0, s.length, SensorP, unit, _, _) 
    	    	&*& array_slice_deep(a, 0, a.length, ActuatorP, unit, _, _);
	@*/

	//@ predicate pre() = RuleInv() &*& [_]TimeUnit_SECONDS(?s) &*& s != null;
	//@ predicate post() = RuleInv() &*& [_]TimeUnit_SECONDS(?s) &*& s != null;

	Sensor[] sensors;
	Actuator[] actuators;
	
	public RainProtecting(Sensor[] sensors, Actuator[] actuators) 
	/*@ requires array_slice_deep(sensors, 0, sensors.length, SensorP, unit, _, _) 
		&*& array_slice_deep(actuators, 0, actuators.length, ActuatorP, unit, _, _)
		&*& [_]TimeUnit_SECONDS(?s) 
		&*& s != null;
	@*/
	//@ ensures pre();
	{
		this.sensors = sensors;
		this.actuators = actuators;
		//@ close RuleInv();
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
			TimeUnit.SECONDS.sleep(REFRESH_RATE);
		}
	}

	public int readSensors() 
	//@ requires RuleInv();
	//@ ensures RuleInv();
	{
		//@ open RuleInv();
		int i = 0;
		int sum = 0;
		while (i < sensors.length)
		//@ invariant sensors |-> ?ss &*& array_slice_deep(ss, i, ss.length, SensorP, unit, _, _);
		{
			//@ array_slice_deep_split(ss, i, i+1);
			//@ assert array_slice_deep(ss, i, i+1, SensorP, unit, _, _);
			//@ assert array_slice_deep(ss, i+1, ss.length, SensorP, unit, _, _);
			
			//@ array_slice_deep_open(ss, i);
			//@ assert array_slice(ss, i, i+1, _);
			///@ assert SensorP(unit, sensors[i], _);
	
			//@ open SensorP(unit, sensors[i], _);
			//@ assert sensors[i] != null;
			///@ assert sensors[i].SensorInv();
			
			Sensor s = sensors[i];
			int v = s.getValue();
			sum += v;
		}
		int avg = sensors.length > 0 ? sum / sensors.length : 0;
		
		return avg;
	}

	public void setActuators(int value) 
	//@ requires RuleInv();
	//@ ensures RuleInv();
	{
		for (int i = 0; i < actuators.length; i++)
		/*@ invariant actuators |-> ?as 
			&*& array_slice_deep(as, 0, as.length, ActuatorP, unit, _, _) 
			&*& 0 <= i 
			&*& i <= as.length;
		@*/
		{
			//@ array_slice_deep_split(as, 0, i);
			//@ array_slice_deep_split(as, i, i+1);
			//@ array_slice_deep_open(as, i);
			//@ open ActuatorP(unit, as[i], _);
			Actuator a = actuators[i];
			//Logger.log.write(a.getName() + " @ BLIMPS #" + Integer.toString(i) + " ON");
			//@ close ActuatorP(unit, as[i], _);
			//@ array_slice_deep_close(as, i, ActuatorP, unit);
			//@ array_slice_deep_join(as, 0);
			//@ array_slice_deep_join(as, 0);
		}
	}

}

class DomoticSystem {
	
	private static final int REFRESH_RATE = 5;

	public static void main(String[] args) throws InterruptedException //@ ensures true;
	/*@ requires [_]System_out(?o) 
		&*& o != null 
		&*& [_]TimeUnit_SECONDS(?ts) 
		&*& ts != null
		&*& Logger_log(?l);
	@*/
	//@ ensures true;
	{

		String[] lightSensorsNames = {"Outside", "Livingroom", "Bedroom", "Kitchen", "Bathroom"};
		Sensor[] lightSensors = new Sensor[5];
 		//@ close Sensor_frac(1/5);
		for (int i = 0; i < lightSensors.length; i++)
		/*@ invariant array_slice_deep(lightSensors, 0, i, SensorP, unit, _, _) &*& 
			array_slice(lightSensors, i, lightSensors.length, _) &*&
			array_slice(lightSensorsNames, i, lightSensorsNames.length, _)
			&*& Sensor_frac(?f);
		@*/
 		{
 			lightSensors[i] = new SensorImpl(lightSensorsNames[i], 0, 100);
			//@ array_slice_deep_close(lightSensors, i, SensorP, unit);
			//@ array_slice_deep_join(lightSensors, 0);
		}
		String[] lampNames = { "Outside", "Livingroom", "Bedroom", "Kitchen", "Bathroom" };
		Actuator[] lamps = new Actuator[5];
		1;
 		//@ close Actuator_frac(1/5);
		for (int i = 0; i < lamps.length; i++)
		/*@ invariant array_slice_deep(lamps, 0, i, ActuatorP, unit, _, _) &*& 
			array_slice(lamps, i, lamps.length, _) &*&
			array_slice(lampNames, i, lampNames.length, _)
			&*& Actuator_frac(?f);
		@*/
 		{
 			lamps[i] = new ActuatorImpl(lampNames[i], 0, 100);
			//@ array_slice_deep_close(lamps, i, ActuatorP, unit);
			//@ array_slice_deep_join(lamps, 0);
		}
	
		new Thread(new IndoorLighting(lightSensors, lamps)).start();
		1;
		
		
		String[] rainSensorsNames = { "At front", "At back", "On roof" };
		Sensor[] rainSensors = new Sensor[3];
 		//@ close Sensor_frac(1/3);
		for (int i = 0; i < rainSensors.length; i++)
		/*@ invariant array_slice_deep(rainSensors, 0, i, SensorP, unit, _, _) &*& 
			array_slice(rainSensors, i, rainSensors.length, _) &*&
			array_slice(rainSensorsNames, i, rainSensorsNames.length, _)
			&*& Sensor_frac(?f);
		@*/
 		{
 			rainSensors[i] = new SensorImpl(rainSensorsNames[i], 0, 100);
			//@ array_slice_deep_close(rainSensors, i, SensorP, unit);
			//@ array_slice_deep_join(rainSensors, 0);
		}
		String[] windowNames = { "Livingroom", "Bedroom", "Kitchen" };
		Actuator[] windows = new Actuator[3];
 		//@ close Actuator_frac(1/3);
		for (int i = 0; i < windows.length; i++)
		/*@ invariant array_slice_deep(windows, 0, i, ActuatorP, unit, _, _) &*& 
			array_slice(windows, i, windows.length, _) &*&
			array_slice(windowNames, i, windowNames.length, _)
			&*& Actuator_frac(?f);
		@*/
 		{
 			windows[i] = new ActuatorImpl(windowNames[i], 0, 100);
			//@ array_slice_deep_close(windows, i, ActuatorP, unit);
			//@ array_slice_deep_join(windows, 0);
		}
		
		new Thread(new RainProtecting(rainSensors, windows)).start();
		
		int last = 0;
		while (true) 
		/*@ invariant [_]System_out(o) 
			&*& o != null 
			&*& [_]TimeUnit_SECONDS(ts) 
			&*& ts != null
			&*& Logger_log(?log);
		@*/
		{
			String[] messages = Logger.getLog().read(last);
			last += messages.length;
			for (int i = 0; i < messages.length; i++) 
			/*@ invariant [_]System_out(o) 
				&*& o != null 
				&*& array_slice(messages, i, messages.length, _);
			@*/			
			{
				// filter message by rule/sensor/actuator/room
				String s = messages[i];
				System.out.println(s);
			}
			TimeUnit.SECONDS.sleep(REFRESH_RATE);
		}
	}
}
