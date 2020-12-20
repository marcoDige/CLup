open util/time

abstract sig Bool{}
one sig TRUE extends Bool{}
one sig FALSE extends Bool{}

abstract sig Person{}

abstract sig StoreClient extends Person{}

sig Employee extends Person{}

sig StoreManager extends Person{}

sig Visitor extends StoreClient{}

sig Customer extends StoreClient{}

sig Location{}

one sig Store{
    location: Location,
    storeManager: StoreManager,
    employees: set Employee,
    capacity: Int,
    realTimeOccupancy: Int one -> Time
} {
    capacity > 0
    all r: realTimeOccupancy.Time | r > 0
}

abstract sig ReservationStatus{}
one sig WAITING extends ReservationStatus{}
one sig CALLED extends ReservationStatus{}
one sig USED extends ReservationStatus{}
one sig EXPIRED extends ReservationStatus{}

abstract sig Reservation{
    client: StoreClient,
    store: Store,
    status: ReservationStatus one -> Time,
    entrance: Entrance lone -> Time
}{
    all t: Time | (entrance.t != none) <=> (status.t = USED)
}

sig Visit extends Reservation{
    informations: VisitInformations
} {
    all t: Time | status.t != CALLED
}

abstract sig LineUpTurn extends Reservation{
    lineUpNumber: Int
}{
    lineUpNumber > 0
}

sig PhysicalLineUpTurn extends LineUpTurn{}

sig VirtualLineUpTurn extends LineUpTurn{
    estimatedQueueTime: Int one -> Time,
    estimatedTravelTime: Int one -> Time,
    qrCode: lone QRCode
}{
    all e: estimatedQueueTime.Time | e >= 0
    all e: estimatedTravelTime.Time | e >= 0
    all t: Time | estimatedQueueTime.t >= estimatedTravelTime.t
}

sig Entrance{
    checkedBy: (Employee + QRCode) lone -> Time
} {
    all t: Time | checkedBy.t != none <=> (some r: Reservation | r.entrance.t = this)
    all t: Time | checkedBy.t in QRCode => (all v: Visit + PhysicalLineUpTurn | not (this in v.entrance.t))
}

sig VisitInformations{
}

sig QRCode{
}

//Each reservation has one entrance
fact {
    all r: Reservation | #r.entrance.Time = 1
}

//LineUpTurn status evolution
fact {
    all t: Time | all l: LineUpTurn | (l.status.t = CALLED) => (not WAITING in l.status.(t.next))
    all t: Time | all l: LineUpTurn | (l.status.t = USED) => (not WAITING in l.status.(t.next) && not CALLED in l.status.(t.next) && not EXPIRED in l.status.(t.next))
    all t: Time | all l: LineUpTurn | (l.status.t = EXPIRED) => (not WAITING in l.status.(t.next) && not CALLED in l.status.(t.next) && not USED in l.status.(t.next))
}

//Visit status evolution
fact {
    all t: Time | all l: Visit | (l.status.t = USED) => (not WAITING in l.status.(t.next) && not EXPIRED in l.status.(t.next))
    all t: Time | all l: Visit | (l.status.t = EXPIRED) => (not WAITING in l.status.(t.next) && not USED in l.status.(t.next))
}

//When a customer is called the queue time equals the travel time
fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = CALLED) => (r.estimatedQueueTime.t = r.estimatedTravelTime.t)
}

//When a VirtualLineUpTurn is expired the queue time and the travel time are 0
fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = EXPIRED) => (r.estimatedQueueTime.t = 0 && r.estimatedTravelTime.t = 0)
}

//When a customer enters the store the queue time and the travel time are 0
fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = USED) => (r.estimatedQueueTime.t = 0 && r.estimatedTravelTime.t = 0)
}

//Different visits have different visit informations
fact {
    all disj v1, v2: Visit | v1.informations != v2.informations
}

//A PhysicalLineUpTurn is associated to a Visitor
fact {
    all r: Reservation | r.client in Visitor <=> r in PhysicalLineUpTurn
}

//Different Reservations have different clients
fact {
    all disj r1, r2: Reservation | r1.client != r2.client
}

//Different Entrances have different QRCodes
fact {
    all disj e1, e2: Entrance | all qr: QRCode | all t: Time | (e1.checkedBy.t = qr) => (e2.checkedBy.t != qr)
}

//Different VirtualLineUpTurns have different QRCodes
fact {
    all disj v1, v2: VirtualLineUpTurn | v1.qrCode != v2.qrCode
}

//An entrance related to a VirtualLineUpTurn is either checked by an employee or it has a qrCode
fact {
    all v: VirtualLineUpTurn | (some e: v.entrance.Time | some emp: Employee | emp in e.checkedBy.Time) => v.qrCode = none
}

//LineUpNumber and estimatedQueueTime relation
fact {
    all disj l1, l2: VirtualLineUpTurn | all t: Time | (l1.estimatedQueueTime.t >= l2.estimatedQueueTime.t) <=> (l1.lineUpNumber > l2.lineUpNumber)
}

//Different LineUpTurns have different LineUpNumbers
fact {
    all disj l1, l2: LineUpTurn | l1.lineUpNumber != l2.lineUpNumber
}

//Store capacity constraint
fact {
    all s: Store | s.realTimeOccupancy.Time <= s.capacity
}

//Different Reservations have different Entrances
fact {
    all disj r1, r2: Reservation | r1.entrance.Time & r2.entrance.Time = none
}

//A Visitor lines up via store, is called and then he/she enters the store
pred VisitorLinesUpAtTheStore[u: Visitor, s: Store, r: PhysicalLineUpTurn, t: Time, emp: Employee] {
    r.client = u
    r.store = s
    r.status.t = WAITING
    r.entrance.t = none
    emp in s.employees
}
pred VisitorIsCalledAtTheStore[u: Visitor, s: Store, r: PhysicalLineUpTurn, t: Time, emp: Employee] {
    VisitorLinesUpAtTheStore[u, s, r, t, emp]
    r.status.t = WAITING
    r.status.(t.next) = CALLED
    r.entrance.(t.next) = none
}
pred VisitorEntersTheStoreAtTheStore[u: Visitor, s: Store, r: PhysicalLineUpTurn, t: Time, e: Entrance, emp: Employee] {
    VisitorIsCalledAtTheStore[u, s, r, t, emp]
    let t' = t.next | (
    r.status.(t') = CALLED and
    r.status.(t'.next) = USED and
    r.entrance.(t'.next) = e and
    s.realTimeOccupancy.(t').next = s.realTimeOccupancy.(t'.next) and 
    e.checkedBy.(t'.next) = emp
    )
}
run VisitorEntersTheStoreAtTheStore for 5 but 3 Time


//A Customer lines up via app, is called and then he/she enters the store normally
pred CustomerLinesUp[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time] {
    r.client = u
    r.store = s
    r.status.t = WAITING
    r.estimatedQueueTime.t > r.estimatedTravelTime.t
    r.entrance.t = none
}
pred CustomerIsCalled[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time] {
    CustomerLinesUp[u, s, r, t]
    r.status.t = WAITING
    r.status.(t.next) = CALLED
    r.estimatedQueueTime.(t.next) = r.estimatedTravelTime.(t.next)
    r.entrance.(t.next) = none
}
pred CustomerEntersTheStore[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time, e: Entrance, emp: Employee] {
    CustomerIsCalled[u, s, r, t]
    let t' = t.next | (
    r.status.(t') = CALLED and
    r.status.(t'.next) = USED and
    r.entrance.(t'.next) = e and
    s.realTimeOccupancy.(t').next = s.realTimeOccupancy.(t'.next) and
    emp in s.employees and 
    e.checkedBy.(t'.next) = emp and
    r.estimatedQueueTime.(t'.next) = r.estimatedTravelTime.(t'.next) and
    r.estimatedQueueTime.(t'.next) = 0
    )
}
run CustomerEntersTheStore for 5 but 3 Time


//A Customer lines up via app, is called and then he/she enters the store with a QRCode
pred CustomerLinesUpQRCode[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time, qr: QRCode] {
    CustomerLinesUp[u, s, r, t]
    r.qrCode = qr
}
pred CustomerIsCalledQRCode[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time, qr: QRCode] {
    CustomerIsCalled[u, s, r, t]
    CustomerLinesUpQRCode[u, s, r, t, qr]
}
pred CustomerEntersTheStoreQRCode[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time, e: Entrance, qr: QRCode] {
    CustomerIsCalledQRCode[u, s, r, t, qr]
    let t' = t.next | (
    r.status.(t') = CALLED and
    r.status.(t'.next) = USED and
    r.entrance.(t'.next) = e and
    r.entrance.(t'.next).checkedBy.(t'.next) = qr and
    s.realTimeOccupancy.(t').next = s.realTimeOccupancy.(t'.next) and
    r.estimatedQueueTime.(t'.next) = r.estimatedTravelTime.(t'.next) and
    r.estimatedQueueTime.(t'.next) = 0
    )
}
run CustomerEntersTheStoreQRCode for 5 but 3 Time


//A Customer books a visit and then enters the store
pred CustomerBooksAVisit[u: Customer, s: Store, r: Visit, t: Time] {
    r.client = u
    r.store = s
    r.status.t = WAITING
    r.entrance.t = none
}
pred CustomerEntersTheStoreVisit[u: Customer, s: Store, r: Visit, t: Time, e: Entrance, emp: Employee] {
    CustomerBooksAVisit[u, s, r, t]
    r.status.(t.next) = USED
    emp in s.employees
    e.checkedBy.(t.next) = emp
    s.realTimeOccupancy.t.next = s.realTimeOccupancy.(t.next)
    r.entrance.(t.next) = e
}
run CustomerEntersTheStoreVisit for 5 but 2 Time