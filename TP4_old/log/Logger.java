package log;

import java.io.*;
import java.util.*;


public class Logger implements Log {

	/*@

	predicate_family_instance Log(this.getClass())(Logger log) =
    		log.messages |-> ?m
    	&*& m != null 
    	&*& foreach<String>(?messages, message) 
    	&*& m.List(messages);

	@*/

	public static final Logger log;
	
	private ArrayList messages;

	private Logger() 
    //@ requires emp;
    //@ ensures Log(this.getClass())(this);
	{
	 	this.log = new Logger();
	 	List m = new ArrayList();
		this.messages = m;
        //@ close foreach<String>(nil, message);
        //@ close Log(this);
	}

	public void write(String message)
	/*//@ requires LogInv(?l);
        //@ ensures LogInv(l);*/
        //@ requires true;
        //@ ensures true;
	{
		//messages.add(message);
	}

	public String[] read(int fromIndex) 
	/*//@ requires [?f]LogInv(?l);
        //@ ensures [f]LogInv(l);*/
        //@ requires true;
        //@ ensures result != null;
	{
		//return messages.subList(fromIndex, size()).toArray(new String[size()]);
		return new String[] {"oi"};
	}

	public int size() 
	/*//@ requires [?f]LogInv(?l);
        //@ ensures [f]LogInv(l);*/
        //@ requires true;
        //@ ensures result >= 0;
	{
		//return messages.size();
		return 0;
	}

}