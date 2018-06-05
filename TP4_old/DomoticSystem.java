import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

import sensors.*;
import actuators.*;
import log.*;
import rules.*;

class DomoticSystem {
	
	private static final int REFRESH_RATE = 5;

	public static void main(String[] args) throws InterruptedException //@ ensures true;
	/*@ requires [_]System_out(?o) &*& o != null 
		&*& [_]TimeUnit_SECONDS(?ts) &*& ts != null 
		&*& Logger_log(?l) &*& l != null;
	@*/
	//@ ensures true;
	{
		String[] lightSensorsNames = {"Outside", "Livingroom", "Bedroom", "Kitchen", "Bathroom"};
		Sensor[] lightSensors = new Sensor[5];
		for (int i = 0; i < lightSensors.length; i++)
		/*@ invariant array_slice_deep(lightSensors, 0, i, SensorP, unit, _, _) &*& 
			array_slice(lightSensors, i, lightSensors.length, _) &*&
			array_slice(lightSensorsNames, i, lightSensorsNames.length, _);
		@*/
 		{
 			lightSensors[i] = new LightSensor(lightSensorsNames[i], 0, 100);
			//@ array_slice_deep_close(lightSensors, i, SensorP, unit);
			//@ array_slice_deep_join(lightSensors, 0);
		}
		String[] lampNames = { "Outside", "Livingroom", "Bedroom", "Kitchen", "Bathroom" };
		Actuator[] lamps = new Actuator[5];
		for (int i = 0; i < lamps.length; i++)
		/*@ invariant array_slice_deep(lamps, 0, i, ActuatorP, unit, _, _) &*& 
			array_slice(lamps, i, lamps.length, _) &*&
			array_slice(lampNames, i, lampNames.length, _);
		@*/
 		{
 			lamps[i] = new Lamp(lampNames[i], 0, 100);
			//@ array_slice_deep_close(lamps, i, ActuatorP, unit);
			//@ array_slice_deep_join(lamps, 0);
		}
	
		new Thread(new IndoorLighting(lightSensors, lamps)).start();
		
		
		
		String[] rainSensorsNames = { "At front", "At back", "On roof" };
		Sensor[] rainSensors = new Sensor[3];
		for (int i = 0; i < rainSensors.length; i++)
		/*@ invariant array_slice_deep(rainSensors, 0, i, SensorP, unit, _, _) &*& 
			array_slice(rainSensors, i, rainSensors.length, _) &*&
			array_slice(rainSensorsNames, i, rainSensorsNames.length, _);
		@*/
 		{
 			rainSensors[i] = new LightSensor(rainSensorsNames[i], 0, 100);
			//@ array_slice_deep_close(rainSensors, i, SensorP, unit);
			//@ array_slice_deep_join(rainSensors, 0);
		}
		String[] windowNames = { "Livingroom", "Bedroom", "Kitchen" };
		Actuator[] windows = new Actuator[3];
		for (int i = 0; i < windows.length; i++)
		/*@ invariant array_slice_deep(windows, 0, i, ActuatorP, unit, _, _) &*& 
			array_slice(windows, i, windows.length, _) &*&
			array_slice(windowNames, i, windowNames.length, _);
		@*/
 		{
 			windows[i] = new Lamp(windowNames[i], 0, 100);
			//@ array_slice_deep_close(windows, i, ActuatorP, unit);
			//@ array_slice_deep_join(windows, 0);
		}
		
		new Thread(new RainProtecting(rainSensors, windows)).start();
		
		
		int last = 0;
		while (true) 
		/*@ invariant [_]System_out(o) &*& o != null 
			&*& [_]TimeUnit_SECONDS(ts) &*& ts != null
			&*& Logger_log(l) &*& l != null;
		@*/
		{
			//String[] messages = Logger.log.read(last);
			String[] messages = {"ola", "adeus"};
			last += messages.length;
			for (int i = 0; i < messages.length; i++) 
			/*@ invariant [_]System_out(o) &*& o != null &*& array_slice(messages, i, messages.length, _);
			@*/			
			{
				//filter message by rule/sensor/actuator/room

				String s = messages[i];
				System.out.println(s);
			}
			TimeUnit.SECONDS.sleep(REFRESH_RATE);
		}
	}
}