class Singleton {

	//@ predicate inv() = true;

	public static final Singleton s;
	
	private Singleton()
	//@ requires emp;
	//@ ensures inv();
	{	
		//@ close inv();
	}
	
	public static Singleton getInstance()
	//@ requires Singleton_s(?singleton) &*& (singleton == null ? true : singleton.inv());
	//@ ensures Singleton_s(result) &*& result.inv();
	{
		if (s == null) {
			s = new Singleton();
		}
		return s;
	}
	
	public void m()
	//@ requires inv();
	//@ ensures inv();
	{}

}

public static void main(String[] args)
//@ requires Singleton_s(?o) &*& o == null;
//@ ensures emp;
{
	while (true)
	//@ invariant Singleton_s(?singleton) &*& (singleton == null ? true : singleton.inv());
	{
		Singleton s = Singleton.getInstance();
		s.m();
	}
}