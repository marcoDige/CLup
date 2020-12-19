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
    status: ReservationStatus -> Time,
    entrance: Entrance lone -> Time
}{

}

sig Visit extends Reservation{
    informations: VisitInformations
} {
    status.Time != CALLED and status.Time != WAITING
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
    checkedBy: Employee
}

sig VisitInformations{
}

sig QRCode{
}

fact {
    all disj l1, l2: VirtualLineUpTurn | all t: Time | (l1.estimatedQueueTime.t >= l2.estimatedQueueTime.t) <=> (l1.lineUpNumber > l2.lineUpNumber)
}

/*
fact {
    all disj l1, l2: LineUpTurn | (l1.lineUpNumber < l2.lineUpNumber and no l1.reservation) => no reservation.l2
}
*/

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
run CustomerLinesUp for 3

pred CustomerIsCalled[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time] {
    CustomerLinesUp[u, s, r, t]
    r.status.t = WAITING
    r.status.(t.next) = CALLED
    r.estimatedQueueTime.(t.next) = r.estimatedTravelTime.(t.next) 
    r.estimatedQueueTime.(t.next) = 0
    r.entrance.(t.next) = none
}
run CustomerIsCalled for 3

pred CustomerEntersTheStore[u: Customer, s: Store, r: VirtualLineUpTurn, t: Time, e: Entrance, emp: Employee] {
    CustomerLinesUp[u, s, r, t]
    CustomerIsCalled[u, s, r, t]
    let t' = t.next | (
    r.status.(t') = CALLED and
    r.status.(t'.next) = USED and
    r.entrance.(t'.next) = e and
    s.realTimeOccupancy.(t').next = s.realTimeOccupancy.(t'.next) and
    emp in s.employees and 
    r.estimatedQueueTime.(t'.next) = r.estimatedTravelTime.(t'.next) and
    r.estimatedQueueTime.(t'.next) = 0
    )
}
run CustomerEntersTheStore for 3

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
    e.checkedBy = emp
    s.realTimeOccupancy.t.next = s.realTimeOccupancy.(t.next)
    r.entrance.(t.next) = e
}
run CustomerEntersTheStoreVisit for 3

pred Show{}
run Show for 3