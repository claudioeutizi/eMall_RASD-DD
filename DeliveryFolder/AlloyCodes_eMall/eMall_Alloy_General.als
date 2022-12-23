open util / integer

//* * * Signatures * * *

sig CF{}
sig OperatorID{}
sig Email{}
sig BusinessEmail{}
sig Password{}

sig Coordinates{
	coordinates: some User,
}

abstract sig User{
	coordinates : one Coordinates,
}

sig Driver extends User{
	cf: one CF,
	email : one Email,
	password : one Password,
	reservation : some Reservation,
}

sig Operator extends User{
	operatorID : one OperatorID,
	businessEmail : one BusinessEmail,
	password : one Password,
	cpo: one CPO,
	cs:some CS,
}

sig Time{
reservation: some Reservation
}

sig Socket{
reservation : some Reservation
}

sig Reservation{ 
	rd: some Driver,	//rd = reservation for drivers
	rs: some Socket,	//rs = reservation for sockets
	time: one Time
}

sig Battery{
	cs: one CS
}

sig Point{
	socket: some Socket,
	cs : one CS	
}

sig CS{ 
	operator : one Operator,
	cpo: one CPO,
	dso: one DSO,
	cp: some Point,
	battery: set Battery,
}

sig CPO{
operator: some Operator,
mydso: one DSO,
}

sig DSO{
	cpo: some CPO,
}




// * * * * * * * * * * Facts * * * * * * * * * * * *
/* * * * * * * * * * * Users * * * * * * * * * * */


//There are no CFs duplicates (each Driver can register just once)
fact CFNODuplicates{
all d1,d2: Driver, thiscf: CF |
thiscf in d1.cf and thiscf in d2.cf implies d1 = d2
}

//There are no email duplicates(each Driver can register just once)
fact EmailNODuplicates{
all d1,d2: Driver, thisemail:  Email |
thisemail in d1.email and thisemail in d2.email implies d1 = d2
}

//There are no OpertorID duplicates
fact OperatorIDNoDuplicate{
all o1,o2: Operator, thisid : OperatorID |
thisid in o1.operatorID and thisid in o2.operatorID implies o1 = o2
}

//There are no business email addresses duplicates
fact BusinessAddressNODuplicates{
all o1,o2: Operator, thisbe:  BusinessEmail |
thisbe in o1.businessEmail and thisbe in o2.businessEmail implies o1 = o2
}

//All OperatorIDs have to be associated to an Operator
fact IDOperatorConnection{
all id : OperatorID | some o:Operator | id in o.operatorID
}

//All business email address have to be associated to an Operator
fact BusinessEmailOperatorConnection{
all bemail : BusinessEmail | some o:Operator | bemail in o.businessEmail
}

//All CFs have to be associated to a Operator
fact CFDriverConnection{
all c: CF | some d: Driver | c in d.cf 
}

//All Email Address have to be associated to an Operator
fact EmailDriverConnection{
all e : Email | some d:Driver | e in d.email
}

//All Password have to be associated to a Driver
fact PasswordDriverConnection{
all p:Password | some d:Driver | p in d.password
}


//All Password have to be associated to a Operator
fact PasswordOperatorConnection{
all p:Password | some o:Operator | p in o.password
}


//Coordinates have one or more Users, and User has only one coordinates
fact MoreUsersCoordinates{
all c : User , u: Coordinates | c in u.coordinates <=> u in c. coordinates
}

// * * * * * * * * * * Facts * * * * * * * * * * * *
/* * * * * * * * * * * Reservations * * * * * * * * * * */

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


//There are no many Times that have the same reservation
fact reservationsNODuplicatesTime{
all r1,r2: Reservation, t:Time |
t in r1.time and t in r2.time implies r1 = r2
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

// * * * * * * * * * * Facts * * * * * * * * * * * *
/* * * * * * * * * * * CPOs * * * * * * * * * * */

//Every CS has one DSO from the same CPO
fact CStoDSOsameCPO{
all s:CS, c:CPO |
c in s.cpo implies s.dso = c.mydso
}

//Every Operator has only one CPO
fact oneOperatortoCPO{
all c1,c2:CPO, o:Operator |
o in c1.operator and o in c2.operator implies c1=c2
}

//Every DSO has only one CPO
fact oneOperatortoCPO{
all c1,c2:CPO, d:DSO |
d in c1.mydso and d in c2.mydso implies c1=c2
}

//Every CP has one and only one CS
fact operatorNoDuplicatesCS{
all c1,c2 : CS , p:Point |
p in c1.cp and p in c2.cp implies c1=c2
}
//Every Socket has one and only one CP
fact socketCP{
all p1,p2 : Point , s:Socket |
s in p1.socket and s in p2.socket implies p1=p2
}
//Every CP has one and only one CS
fact operatorNoDuplicatesCS{
all c1,c2 : CS , p:Point |
p in c1.cp and p in c2.cp implies c1=c2
}
//Every Battery has one and only one CS
fact batteriesInCS{
all c1,c2 : CS, b:Battery |
b in c1.battery and b in c2.battery implies c1 = c2
}



//Connection between Operator and CPO
fact connectionOperatortoCPO{
all o:Operator, c:CPO |
o in c.operator <=> c in o.cpo
}

/*
We have that: DSO can have more different CPOs, but every CPO has only one DSO and
every CS of the same  CPO has one DSO of the CPO
*/

// If we want that every CPO must have only one DSO and viceversa: uncomment this
/*
//Connection between DSO and CPO
fact connectionDSOandCPO{
all d:DSO, c:CPO |
d in c.dso<=> c in d.cpo
}
*/

//Connection between Operator and CS
fact connectionOperatortoCS{
all o:Operator, c:CS |
o in c.operator <=> c in o.cs
}

//Connection between CS and CPO of the same Operator
fact connectionCStoCPO{
all s:CS, o:Operator | 
s in o.cs and o in s.operator implies s.cpo = o.cpo
}

//Connection between Operator and CS
fact connectionPointToCS{
all c : CS, p : Point | c in p.cs <=> p in c.cp
}
//Connection between Operator and CS
fact connectionBatteriesCS{
all b:Battery | some c:CS | b in c.battery
}

//Connection between batteries and CS
fact batteryAndCS{
all b: Battery, c: CS | b in c.battery <=> c in b.cs
}

//There are CPs with at least one Socket
fact moreSocketInCP{
all p:Point | #p.socket >=2
}
//There are CS with more batteries
fact morebatteriesInCS{
all c:CS | #c.battery <=3
}




//* * * * * * * * * * Predicates* * * * * * * * * *
pred show{
#Operator >=2
#Driver=2
#Reservation >=2
#CS >=2
#CPO>=2
}

run show for 10
