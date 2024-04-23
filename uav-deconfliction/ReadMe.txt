One-lane model
--------
In the one-lane Forge model, UAV is a  sig  with two fields:  speed  and  tentry  (launch time). The current state at any timestep is modeled as  sig DeconfState  with a field pointing to zero or one next state, an integer field representing the timestep, and a function field mapping  UAV  to its position in the lane ( Int ). The model also includes predicates to check validity of states, detect initial and final states, detect whether two UAVs are simultaneously traveling along the lane, and decide safety (deconfliction) of the UAVs.

The launch time and speed of the first UAV and the desired launch interval of the second UAVs can be set in the  presetUAVs  predicate. Alternatively, the two UAVs and their fields can also be specified in the concrete instance  uav_example  and that instance can be passed to  run . Although this model is tested with just two UAVs, the validity and safety predicates have been written in a general enough fashion so that it can work with more UAVs too.

Multi-lane model
----------
The multi-lane model has three main  sig s.
Lane		has one integer field  length .
UAV		has three fields:  tlaunch  (integer),  speed  (integer), and
		path  - a sequence of  Lane s (i.e.  pfunc Int -> Lane ).
UAVState	has three variable fields:  time  (current timestep),
		laneOf  (maps  UAV  to the  Lane  it is currently flying through), and
		positionOf  (maps  UAV  to its current position in that  Lane ).
		These three can change with time.

The multi-lane model also consists of predicates to ensure validity, decide initial and final states, determine change in the time-varying parameters of  UAVState , and decide safety (deconfliction) of the UAVs. The model can be tested by supplying different concrete instances to  run , however it is `Unsatisfiable' as of date.  

I do not model liveness properties in either model.