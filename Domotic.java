
class Logger() {
	public static final Logger log = new Logger();

	private ArrayList messages;

	private Logger() {}


	void write(String message) 

	String get(int i)

	int size()

	String[] get(nlines)
}

class abtract AbstractRule {

}


class IndorLighting extend AbstractRule implements Runnable {

IndorLighting(Sensor[] ss, Actuator[] as)

	run() {
		if (ss...) {
			aa..
		}
	}
}



main() {
	Sensor[] sensors = new Sensor[] { 
		new LightSensor(nome:"outside"),
		new LightSensor(nome:"corner1"),
		new LightSensor(nome:"corner2"),
		new LightSensor(nome:"corner3"),

	}
	Atuator[] actuator = new Actuator[] {
		new Lamp(nome:"Big")
	}
	new Thread(new IndoorLighting(sensors, actuators)).start();
	while(true) {
		Logger.log.get();
		system.out.println(messages);
		Timeunit.SECONDS.sleep(REFRESH_RATE);
	}

}