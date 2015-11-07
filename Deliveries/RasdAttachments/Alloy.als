//----------------SIGNATURES-----------------------

// we have to distinguish between a Driver who is taking care of a request and 
// an available Driver who is inserted into a queue and is waiting for new requests
abstract sig MyTaxiDriver{}

sig AvailableDriver extends MyTaxiDriver{
	isMember: one TaxiQueue
}

sig UnavailableDriver extends MyTaxiDriver{
	//this is a relation for a taxi and its passengers
	serving : some User
}


sig User{
	request: lone Request,
	reservation: set Reservation	
}

// A request have to be referred to a zone .
// We have two different possible instances for a request: a simple one or a sharing one
abstract sig Request{
	requestedBy:one User,
	where:one Zone
}

// We have these two apparently usless signatures to underline that a user can own
// different types of request
sig SimpleRequest extends Request {}
sig SharingRequest extends Request{}


sig Reservation{
	reservedBy: one User,
	date: one Date,
	where: one Zone
}

// We define this signature to represent date and time of a reservation
sig Date{}

// Each zone must have only one queue, and this may contains some available taxi
// We define a contiguity relation between zones
sig TaxiQueue{
	zone : one Zone,
	waiting : set AvailableDriver
}


sig Zone{
	queue : one TaxiQueue,
	contiguous : some Zone
}




//-------------------FACTS-----------------------

// Constraints on drivers:
fact unavailableDriverFeatures{
	// the impossibility of having a user served by two distinct taxi,
	all u : User | no disj ud1, ud2 : UnavailableDriver | (u in ud1.serving) && (u in ud2.serving)
	// we impose the maximum of four passengers for each taxi
	all u: UnavailableDriver | #u.serving<5
}

fact availableDriverFeatures{
	// the impossibility of having the same available taxi in two distinct queues
	all a : AvailableDriver | no disj q1, q2 : TaxiQueue | (a in q1.waiting) && (a in q2.waiting)	
	// an avilable taxi must be inserted in a queue
	no a : AvailableDriver | #a.isMember=0
}


//Constraints on zones:
fact zoneFeatures{
	//we impose the maximum of 8 zone contigous to one
	all z : Zone | #z.contiguous < 8
	//a zone can't be contigous of itself 
	no z : Zone | z in z.contiguous
	//if a zone is contigous to one other, this other is contigous to the previous one
	all z, z' : Zone | (z' in z.contiguous) <=> (z in z'.contiguous)
}


//contraints on TaxiQueues:
fact taxiQueuesFeatures{
	//each zone has a unique Taxi queue and a Taxi queue refers to a unique zone
	all q : TaxiQueue | all z : Zone | (q in z.queue) <=> (z in q.zone)
	//each AvaiableDriver belongs to a unique queue
	all q : TaxiQueue | all a : AvailableDriver | (q in a.isMember) <=> (a in q.waiting)
}


//contraints on  Request:
fact requestFeatures{
	// if a user has requested a taxi, the taxi has received a request from the user
	all u :User | all r: Request  | (r in u.request) <=> (u in r.requestedBy)
	// if a taxi is unvailable cannot receive other requests
	no u:User, t:UnavailableDriver,r:Request | (u in t.serving) && (u in r.requestedBy)	
}

//constraints on Reservation
fact reservationFeatures{
	// there's a bijective relation beetwen the reservation and the reserver user
	all u :User | all r: Reservation | (r in u.reservation) <=> (u in r.reservedBy)
	// a user cannot have two reservation in the same date
	no u:User,r,r':Reservation |r!=r'&&r in u.reservation && r' in u.reservation && r.date=r'.date
	// a reservation must be related to one and only one user
	no u,u':User| u!=u' && u.reservation = u'.reservation && #u.reservation!=0
	// cannot exists a date not related with a reservation
	all d: Date, r: Reservation | d=r.date
}




//-------------------ASSERTIONS----------------

// We want to verify that a user can't request a taxi while he's passenger on a taxi
assert NoRequestFromUserServed{
	no u:User, t:UnavailableDriver,r:Request | (u in t.serving) && (u in r.requestedBy)
}
//check NoRequestFromUserServed

// We want to verify that a taxi can't have more than four passengers 
assert NumberOfPassengers{
	no u: UnavailableDriver | #u.serving>4
}
//check NumberOfPassengers





//-------------------PREDICATES---------------

//Show the entire world
pred show{}
run show for 6


//Show a world that contains TaxiDrivers associated to their Queues and then to their Zones
pred showQueueZoneTaxi{
	#MyTaxiDriver>1
	#TaxiQueue>1
}
run showQueueZoneTaxi for 7 but 0 UnavailableDriver, 0 User, 0 Request, 0 Reservation, 0 Date


//Show a world that contains at least one reservation and the associated elements
pred showReservations{
	#Reservation>0
}
run showReservations for 5 but 0 Request, 0 MyTaxiDriver


//Show a world that contains the different types of request and their related users
pred showRequests{
	#SimpleRequest=2
	#SharingRequest=1
	#User=3
}
run showRequests for 10 but 0 Reservation, 0 Date, 0 MyTaxiDriver


//Show a world that contains unavailable taxis which are serving some users
pred showUnavailableTaxi{
	#UnavailableDriver>1
}
run showUnavailableTaxi for 10 but 0 Request, 0 Reservation, 0 Date, 0 Zone, 0 TaxiQueue











