import java.util.concurrent.*;
import java.util.Random;
import java.util.concurrent.locks.*;
import java.util.ArrayList;
import java.util.List;


interface Sensor {
	//@ predicate Sensor();
	
 	String getName();
	//@ requires Sensor();
	//@ ensures Sensor();

}

abstract class  SensorAbs implements Sensor {

	public abstract String getName();
	//@ requires Sensor();
	//@ ensures Sensor();
}

class SensorImpl extends SensorAbs {

	private String name;

	//@ predicate Sensor() = this.name |-> ?v &*& v != null;
	
	SensorImpl(String name)
	//@ requires true &*& name != null;
	//@ ensures Sensor();
	{ this.name = name; }

	public String getName()
	//@ requires Sensor();
	//@ ensures Sensor();
	{
		return name;
	}
}


public static void main(String[] args) 
//@ requires true;
//@ ensures true;
{
	SensorImpl s = new SensorImpl("ola");
}

