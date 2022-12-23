open util / integer

// * * * * * * * * * * Signatures * * * * * * * * * * 

sig Time{
	reservation: some Reservation,
}

sig Driver{
	reservation : some Reservation,
}

sig Socket{
	reservation : some Reservation,
}

sig Reservation{ 
	rd: some Driver,	//rd = reservation for drivers
	rs: some Socket,	//rs = reservation for sockets
	time: one Time
}

// * * * * * * * * * * Facts * * * * * * * * * * 

//There are not many Drivers that have the same reservation
fact reservationsNODuplicatesDriver{
all d1,d2: Driver, r: Reservation |
r in d1.reservation and r in d2.reservation implies d1 = d2
}

//There are not many Sockets that have the same reservation
fact reservationsNODuplicatesSockets{
all s1,s2: Socket, r: Reservation |
r in s1.reservation and r in s2.reservation implies s1 = s2
}

//There are not many Sockets that have the same reservation
fact moreReservationsInDifferentTimes{
all d:Driver, r1,r2:Reservation |
(r1 in d.reservation and d in r1.rd) and
(r2 in d.reservation and d in r2.rd) and
r1 != r2 implies r1.time != r2.time
}

//There are not many Sockets that have the same reservation
fact moreReservationsInDifferentTimes{
all s:Socket, r1,r2:Reservation |
(r1 in s.reservation and s in r1.rs) and
(r2 in s.reservation and s in r2.rs) and
r1 != r2 implies r1.time != r2.time
}


//Connection between Time and Reservation: Time must have one Reservation
fact connectionTimeReservation{
all t : Time , r: Reservation |  r in t.reservation <=> t in r.time
}

//Connection between Drive and Reservation
fact connectionDriverReservation{
all d : Driver , r: Reservation | d in r.rd <=> r in d.reservation
}

//Connection between Socket and Reservation
fact connectionSocketReservation{
all s : Socket , r: Reservation | s in r.rs <=> r in s.reservation
}

//* * * * * * * * * * Predicates* * * * * * * * * *

pred show{
#Socket >=3
#Driver >=2
#Reservation>=2
}
run show for 10





