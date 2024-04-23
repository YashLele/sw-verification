#lang forge/temporal

option max_tracelength 25
// Safety distance 3

sig Lane {
    length : one Int
}

pred validLanes {
    all l:Lane | l.length > 0
}

sig UAV {
    tlaunch : one Int,
    speed : one Int,
    path : pfunc Int -> Lane
}

pred validUAVs {
    all u:UAV | {
        u.tlaunch >= 0
        u.speed >= 0
        isSeqOf[u.path, Lane]
        (not (isEmpty[u.path] or hasDups[u.path]))
        min[inds[u.path]] = 0
    }
}

sig UAVState {
    var time : one Int,
    var laneOf : pfunc UAV -> Lane,
    var positionOf : pfunc UAV -> Int
}

pred validState[s: UAVState] {
    s.time >= 0
    all u : UAV {
        s.laneOf[u] = none <=> s.positionOf[u] = none
        s.time < u.tlaunch => s.laneOf[u] = none
        s.time = u.tlaunch => (s.laneOf[u] = u.path[0] and s.positionOf[u] = 0)
        s.laneOf[u] != none => (let lu = s.laneOf[u] | s.positionOf[u] >= 0 and s.positionOf[u] <= lu.length)
    }
    //all disj s1, s2: UAVState | s1.time != s2.time
}

pred init [s : UAVState] {
    s.time = 0
    /* The following constraint will not be required because 'validStates' constraints will take care of it
    all u: UAV {
        u.tlaunch = 0 => s.laneOf[u] = u.path[0] else s.laneOf[u] = none
        s.laneOf[u] != none => s.laneOf[u] = u.path[0]
    }*/
}

pred final [s : UAVState] {
    s.time' = s.time
}

fun nextPosition[pos: Int, spd : Int, laneLength: Int] : one Int {
    let newPos = add[pos, spd] |
        newPos >= laneLength => subtract[newPos, laneLength] else newPos
}

fun nextLane[currLane: Lane, pos: Int, u: UAV] : lone Lane {

    //TODO: This is not going to work. Fix this directly in 'tick'.

    let newPos = add[pos, u.speed] |
        newPos >= currLane.length => (seqLast[u.path] = currLane => none else u.path[add[idxOf[u.path, currLane],1]]) else currLane
}

pred tick[s : UAVState] {
    (all u:UAV | (s.time > u.tlaunch and s.laneOf[u] = none)) => s.time' = s.time else s.time' = add[s.time, 1]
    all u:UAV {
        // 'validStates' will take care of the following
        // s.laneOf[u] = none => (s.time' = u.tlaunch => (s.laneOf'[u] = u.path[0] and s.positionOf'[u] = 0))

        //s.laneOf[u] != none => s.laneOf'[u] = nextLane[s.laneOf[u], s.positionOf[u], u]

        let currLane = s.laneOf[u] | currLane != none => (add[s.positionOf[u], u.speed] < currLane.length => s.laneOf'[u]=currLane else s.laneOf'[u] = u.path[add[1, idxOf[u.path, currLane]]])

        (s.positionOf[u] != none and s.laneOf'[u] != none) => (let lu = s.laneOf[u] | s.positionOf'[u] = nextPosition[s.positionOf[u], u.speed, lu.length]) else s.positionOf'[u] = none
        
        //TODO: HANDLE THE CASE OF LAST LANE FOR TICK !!!! especially laneOf

    }
}

pred deconflicted[s: UAVState] {
    all disj u1, u2 : UAV {
        (s.laneOf[u1] != none and s.laneOf[u2] != none and s.laneOf[u1] = s.laneOf[u2]) => abs[subtract[s.positionOf[u1], s.positionOf[u2]]] >= 3
    }
}

//pred presetUAVs

run {
    validLanes
    validUAVs
    all s : UAVState | init[s]    
    all s : UAVState | always validState[s]
    all s : UAVState | tick[s] and eventually final[s]
    all s : UAVState | always deconflicted[s]
} for exactly 1 UAVState, exactly 2 UAV, exactly 3 Lane
  for {
    Lane = `L1 + `L2 + `L3
    UAV = `U1 + `U2
    `U1.tlaunch = 1
    `U1.speed = 4
    `U1.path = 0 -> `L1 +
               1 -> `L3
    `U2.speed = 6
    `U2.path = 0 -> `L2 +
               1 -> `L3
    length in `L1 -> 10 +
              `L2 -> 12 +
              `L3 -> 10
  }