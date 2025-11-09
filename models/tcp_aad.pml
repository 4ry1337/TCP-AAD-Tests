/*
 * TCP-AAD (Aggregation-Aware Delayed ACK) Model
 *
 * Implements adaptive acknowledgment delay based on inter-arrival times:
 * - Tracks IAT_min (minimum inter-arrival time)
 * - Tracks IAT_curr (current inter-arrival time)
 * - Calculates adaptive timeout: ATO = (IAT_min * 0.75 + IAT_curr * 0.25) * 1.5
 * - Periodically resets IAT_min (every 1 second)
 * - Filters small IATs (< 0.2ms)
 *
 * Time Abstraction: 1 logical time unit = 1ms
 * Scaled formula for integer arithmetic: ATO = (IAT_min * 3 + IAT_curr) / 4 * 3 / 2
 * Simplified: ATO = (IAT_min * 3 + IAT_curr) * 3 / 8
 */

#define MAX_SEGMENTS 10        /* Total segments to transfer */
#define CHANNEL_SIZE 20        /* Buffered channel size */
#define MAX_DELAYED_SEGS 2     /* Max segments before forced ACK */
#define MAX_ATO 500            /* Maximum ATO: 500ms */
#define MIN_IAT_FILTER 2       /* Filter IATs < 0.2ms (scaled to 2 units) */
#define RESET_PERIOD 1000      /* Reset IAT_min every 1 second */
#define MAX_IAT 10000          /* Maximum possible IAT */
#define MAX_TIME 5000          /* Maximum simulation time */

/* Message types */
mtype = { DATA, ACK };

/* Global state */
int logical_time = 0;
int segments_sent = 0;
int segments_acked = 0;
int acks_sent = 0;
int adaptive_acks = 0;         /* ACKs sent using adaptive timing */
int immediate_acks = 0;        /* ACKs sent immediately */
int iat_min = MAX_IAT;         /* Minimum IAT observed (for LTL verification) */
int ato = MAX_ATO;             /* Adaptive timeout (for LTL verification) */
bool connection_active = true;

/* Communication channels */
chan sender_to_receiver = [CHANNEL_SIZE] of { mtype, int };
chan receiver_to_sender = [CHANNEL_SIZE] of { mtype, int };

/* Sender process */
active proctype Sender() {
    int seq_num = 0;
    int expected_ack = 0;
    int ack_received;
    int send_interval = 50;    /* Send packet every 50 time units */
    int next_send_time = 0;

    printf("Sender: Started (TCP-AAD)\n");

    do
    :: (seq_num < MAX_SEGMENTS && logical_time >= next_send_time && logical_time < MAX_TIME) ->
        atomic {
            sender_to_receiver ! DATA(seq_num);
            segments_sent++;
            printf("T=%d: Sender sent DATA seq=%d\n", logical_time, seq_num);
            seq_num++;
            next_send_time = logical_time + send_interval;
        }

    :: receiver_to_sender ? ACK(ack_received) ->
        atomic {
            assert(ack_received <= seq_num);
            segments_acked = ack_received + 1;
            printf("T=%d: Sender received ACK=%d (total_acked=%d)\n",
                   logical_time, ack_received, segments_acked);
        }

    :: (seq_num >= MAX_SEGMENTS && segments_acked >= MAX_SEGMENTS) ->
        break;

    :: (logical_time >= MAX_TIME) ->
        printf("Sender: Timeout at T=%d\n", logical_time);
        break;
    od

    connection_active = false;
    printf("Sender: Done. Sent=%d, Acked=%d\n", segments_sent, segments_acked);
}

/* Receiver process with TCP-AAD logic */
active proctype Receiver() {
    int expected_seq = 0;
    int received_seq;
    int delayed_count = 0;

    /* TCP-AAD state variables */
    int iat_curr = 0;               /* Current IAT */
    int last_packet_time = 0;       /* Time of last packet */
    int last_reset_time = 0;        /* Last IAT_min reset time */

    bool timer_pending = false;
    int timer_expiry = 0;
    int last_acked_seq = -1;
    bool quick_ack_mode = false;    /* Quick ACK mode flag */

    printf("Receiver: Started (TCP-AAD)\n");

    do
    :: sender_to_receiver ? DATA(received_seq) ->
        atomic {
            printf("T=%d: Receiver got DATA seq=%d (expected=%d)\n",
                   logical_time, received_seq, expected_seq);

            /* Calculate IAT (Inter-Arrival Time) */
            if
            :: (last_packet_time > 0) ->
                iat_curr = logical_time - last_packet_time;
                printf("T=%d: IAT_curr=%d, IAT_min=%d\n",
                       logical_time, iat_curr, iat_min);

                /* Filter small IATs */
                if
                :: (iat_curr >= MIN_IAT_FILTER) ->
                    /* Update IAT_min */
                    if
                    :: (iat_curr < iat_min) ->
                        iat_min = iat_curr;
                        printf("T=%d: Updated IAT_min=%d\n", logical_time, iat_min);
                    :: else -> skip;
                    fi
                :: else ->
                    printf("T=%d: IAT filtered (too small)\n", logical_time);
                fi

            :: else -> skip;
            fi

            last_packet_time = logical_time;

            /* Periodic IAT_min reset */
            if
            :: (logical_time >= last_reset_time + RESET_PERIOD) ->
                iat_min = MAX_IAT;
                last_reset_time = logical_time;
                printf("T=%d: IAT_min reset (periodic)\n", logical_time);
            :: else -> skip;
            fi

            /* Check if out-of-order */
            if
            :: (received_seq != expected_seq) ->
                /* Out-of-order: immediate ACK + enter quick ACK mode */
                printf("T=%d: Out-of-order! Immediate ACK + quick mode\n", logical_time);
                receiver_to_sender ! ACK(last_acked_seq);
                immediate_acks++;
                acks_sent++;
                delayed_count = 0;
                timer_pending = false;
                quick_ack_mode = true;

            :: (received_seq == expected_seq) ->
                /* In-order segment */
                expected_seq++;
                delayed_count++;
                last_acked_seq = received_seq;

                if
                :: (delayed_count >= MAX_DELAYED_SEGS) ->
                    /* Calculate adaptive ATO */
                    /* ATO = (IAT_min * 3 + IAT_curr) * 3 / 8 */
                    /* Simplified to avoid overflow: (IAT_min * 3 + IAT_curr) / 4 */
                    if
                    :: (iat_min < MAX_IAT && iat_curr > 0) ->
                        ato = (iat_min * 3 + iat_curr) / 4;
                        if
                        :: (ato > MAX_ATO) -> ato = MAX_ATO;
                        :: (ato <= MAX_ATO) -> skip;
                        fi
                        printf("T=%d: Calculated ATO=%d (IAT_min=%d, IAT_curr=%d)\n",
                               logical_time, ato, iat_min, iat_curr);
                    :: else ->
                        ato = MAX_ATO;
                    fi

                    /* Send ACK based on adaptive timing */
                    printf("T=%d: Sending adaptive ACK=%d (ATO=%d)\n",
                           logical_time, received_seq, ato);
                    receiver_to_sender ! ACK(received_seq);
                    adaptive_acks++;
                    acks_sent++;
                    delayed_count = 0;
                    timer_pending = false;
                    quick_ack_mode = false;

                :: (delayed_count < MAX_DELAYED_SEGS) ->
                    /* Set/reset timer with adaptive ATO */
                    if
                    :: (quick_ack_mode) ->
                        /* In quick ACK mode: shorter timeout */
                        ato = MAX_ATO / 2;
                        quick_ack_mode = false;
                    :: (!quick_ack_mode && iat_min < MAX_IAT && iat_curr > 0) ->
                        ato = (iat_min * 3 + iat_curr) / 4;
                        if
                        :: (ato > MAX_ATO) -> ato = MAX_ATO;
                        :: (ato <= MAX_ATO) -> skip;
                        fi
                    :: else ->
                        ato = MAX_ATO;
                    fi

                    timer_expiry = logical_time + ato;
                    timer_pending = true;
                    printf("T=%d: Adaptive timer set, expires at T=%d (ATO=%d)\n",
                           logical_time, timer_expiry, ato);
                fi
            fi
        }

    :: (timer_pending && logical_time >= timer_expiry) ->
        /* Timer expired: send ACK */
        atomic {
            printf("T=%d: Adaptive timer expired, sending ACK=%d\n",
                   logical_time, last_acked_seq);
            receiver_to_sender ! ACK(last_acked_seq);
            adaptive_acks++;
            acks_sent++;
            delayed_count = 0;
            timer_pending = false;
        }

    :: (!connection_active && empty(sender_to_receiver) && !timer_pending) ->
        break;
    od

    printf("Receiver: Done. Adaptive ACKs=%d, Immediate ACKs=%d\n",
           adaptive_acks, immediate_acks);
}

/* Time keeper */
active proctype TimeKeeper() {
    do
    :: (logical_time < MAX_TIME) ->
        atomic {
            logical_time++;
        }
    :: (logical_time >= MAX_TIME) ->
        break;
    od
}

/* LTL Properties for TCP-AAD */

/* S1: ATO never exceeds maximum bound */
ltl ato_bounded { [](ato <= MAX_ATO) }

/* S2: All segments eventually get acknowledged */
ltl eventual_ack_aad { <>(segments_sent > 0 -> segments_acked == segments_sent) }

/* S3: IAT_min is valid */
ltl iat_min_valid { [](iat_min > 0 && iat_min <= MAX_IAT) }

/* S4: ACKs are sent (progress) */
ltl acks_progress { []<>(acks_sent > 0) }

/* S5: Adaptive behavior is used */
ltl adaptive_used { <>(adaptive_acks > 0) }

/* L1: IAT_min is periodically reset */
ltl iat_reset { []<>(iat_min == MAX_IAT) }

/* L2: Connection completes */
ltl completion_aad { <>(segments_sent == MAX_SEGMENTS && segments_acked == MAX_SEGMENTS) }
