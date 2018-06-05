package log;

//@ predicate string_non_null(String s) = s != null; 

//@ predicate_family Log(Class c)(Log l);

interface Log {

	/**
	 * Write a message to the log
	 * @param message the message to write
	 */
	void write(String message);
	//@ requires Log(this.getClass())(this);
	//@ ensures Log(this.getClass())(this);

	/**
	 * Read all messages since index to the end of the log
	 * @param fromIndex the index
	 * @return the messages
	 */
	String[] read(int fromIndex);
	//@ requires Log(this.getClass())(this);
	//@ ensures Log(this.getClass())(this);

	/**
	 * Get size of the log
	 * @return the size
	 */
	int size();
	//@ requires Log(this.getClass())(this);
	//@ ensures Log(this.getClass())(this);

}
