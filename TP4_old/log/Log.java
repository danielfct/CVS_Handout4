package log;

/*
Daniel Filipe Santos Pimenta 45404
CVS Handout 4 - Verifast Domotic System
 */

interface Log {

	//@ predicate LogInv(Logger l);
	/**
	 * Write a message to the log
	 * @param message the message to write
	 */
	void write(String message);
	//@ requires LogInv(?l);
	//@ ensures LogInv(l);

	/**
	 * Read all messages since index to the end of the log
	 * @param fromIndex the index
	 * @return the messages
	 */
	String[] read(int fromIndex);
	//@ requires [?f]LogInv(?l);
	//@ ensures [f]LogInv(l);

	/**
	 * Get size of the log
	 * @return the size
	 */
	int size();
	//@ requires [?f]LogInv(?l);
	//@ ensures [f]LogInv(l);

}
