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

fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = CALLED) => (r.estimatedQueueTime.t = r.estimatedTravelTime.t)
}

fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = EXPIRED) => (r.estimatedQueueTime.t = 0 && r.estimatedTravelTime.t = 0)
}

fact {
    all t: Time | all r: VirtualLineUpTurn | (r.status.t = USED) => (r.estimatedQueueTime.t = 0 && r.estimatedTravelTime.t = 0)
}

fact {
    all v1, v2: Visit | v1.informations != v2.informations
}

fact {
    all r: Reservation | r.client in Visitor <=> r in PhysicalLineUpTurn
}

fact {
    all disj r1, r2: Reservation | r1.client != r2.client
}

fact {
    all disj e1, e2: Entrance | all qr: QRCode | all t: Time | (e1.checkedBy.t = qr) => (e2.checkedBy.t != qr)
}

fact {
    all disj v1, v2: VirtualLineUpTurn | v1.qrCode != v2.qrCode
}

fact {
    all v: VirtualLineUpTurn | (some e: v.entrance.Time | some emp: Employee | emp in e.checkedBy.Time) => v.qrCode = none
}

fact {
    all disj l1, l2: VirtualLineUpTurn | all t: Time | (l1.estimatedQueueTime.t >= l2.estimatedQueueTime.t) <=> (l1.lineUpNumber > l2.lineUpNumber)
}

fact {
    all disj l1, l2: LineUpTurn | l1.lineUpNumber != l2.lineUpNumber
}

fact {
    all s: Store | s.realTimeOccupancy.Time <= s.capacity
}

fact {
    all disj r1, r2: Reservation | r1.entrance.Time & r2.entrance.Time = none
}

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
    r.estimatedQueueTime.(t.next) = 0
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

pred Show{}
run Show for 3