#lang froglet

// Not writing a Lane sig because this whole file is for 2 flights in a single lane.
// So, just using a DeconfState instead, which will capture the current state (at each timestep) of the lane and 2 UAVs.

// THIS MODEL ASSUMES A LANE OF LENGTH 10 UNITS AND HEADWAY DISTANCE OF 3 UNITS
// UAV position -1 => UAV has not entered the lane yet
// UAV position 11 => UAV has exited the lane

option verbose 2

//abstract
sig UAV {
    speed: one Int,
    tentry: one Int
}
//one sig U1 extends UAV {}
//one sig U2 extends UAV {}

sig DeconfState {
    nxtSt: lone DeconfState,
    timestep: one Int,
    position: pfunc UAV -> Int
}

inst uav_example {
    UAV = `U1 + `U2
    speed = `U1 -> 2 +
            `U2 -> 3
    tentry = `U1 -> 3 +
             `U2 -> 6
    nxtSt is linear
}

pred presetUAVs {
    one u1:UAV | {u1.speed = 2 and u1.tentry = 3}
    one u2:UAV | {u2.speed = 3 and u2.tentry >= 0 and u2.tentry <= 9}
}

/*pred genericValidUAVs {
    all u:UAV | {u.speed > 0 and u.tentry >= 0}
}*/

pred initState[s: DeconfState] {
    s.timestep = 0
    all u:UAV {u.tentry >= 0 and u.speed > 0 and u.speed < 5}
    all u:UAV {u.tentry = 0 => s.position[u] = 0 else s.position[u] = -1}
}

pred finalState[s: DeconfState] {
    all u:UAV {s.position[u] = 11}
}

pred isInLane[u: UAV, s: DeconfState] {
    s.position[u] >= 0 and
    s.position[u] <= 10
}

pred validStates {
    all s: DeconfState, u: UAV | {
        s.timestep >= 0 and
        s.position[u] >= -1 and
        s.position[u] <= 11
    }
    // Just to be extra careful to ensure only 2 UAVs
    // #{u:UAV | isInLane[u,s]} <= 2
    // This is ideally specified as 'exactly 2 UAV' bound for the 'run'
}

pred bothInLane[u1: UAV, u2: UAV, s: DeconfState] {
    isInLane[u1, s] and
    isInLane[u2, s]
}

pred safeState[s: DeconfState] {
    all disj u1, u2 : UAV {
        bothInLane[u1, u2, s] => (abs[subtract[s.position[u1], s.position[u2]]] >= 3)
    }
}

pred validNextState[s1: DeconfState, s2: DeconfState] {
    s2.timestep = add[s1.timestep, 1]
    all u:UAV {
        //min[add[s1.position[u], u.speed], 11]
        s1.position[u] >= 0 implies s2.position[u] = (add[s1.position[u], u.speed] > 10 => 11 else add[s1.position[u], u.speed]) else (u.tentry = s2.timestep implies s2.position[u] = 0 else s2.position[u]=-1)
        // This huge line is equivalent to:
        // if s1.position[u] >= 0:
        //      if s1.position[u] + u.speed > 10:
        //          s2.position[u] = 11
        //      else:
        //          s2.position[u] = s1.position[u] + u.speed
        // else:
        //      if u.tentry == s2.timestep:
        //          s2.position[u] = 0
        //      else:
        //          s2.position[u] = -1
    }
}

pred validTransitions {
    some si, sf : DeconfState {
        initState[si]
        finalState[sf]
        no s:DeconfState | s.nxtSt = si
        no s:DeconfState | sf.nxtSt = s
        all s:DeconfState | s != si => reachable[s, si, nxtSt]
    }
    all s:DeconfState | s.nxtSt != none => validNextState[s, s.nxtSt]
}

pred deconflicted {
    all s:DeconfState | safeState[s]
}

run {
    presetUAVs // remove this if using uav_example
    validStates
    validTransitions
    deconflicted
} for exactly 2 UAV, 14 DeconfState, 5 Int
  for {nxtSt is linear} // or uav_example