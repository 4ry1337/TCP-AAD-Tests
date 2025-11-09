/*
 * TCP Default Delayed ACK Model (Linux RFC 1122 Implementation)
 *
 * Implements the standard delayed acknowledgment mechanism:
 * - ACK every 2 full-sized segments
 * - ACK timeout: 500ms (500 time units)
 * - Immediate ACK on out-of-order segments
 *
 * Time Abstraction: 1 logical time unit = 1ms
 */

#define MAX_SEGMENTS 10     /* Total segments to transfer */
#define CHANNEL_SIZE 20     /* Buffered channel size */
#define MAX_DELAYED_SEGS 2  /* RFC 1122: ACK at least every 2 segments */
#define ACK_TIMEOUT 500     /* 500ms timeout */
#define MAX_TIME 5000       /* Maximum simulation time */

/* Message types */
mtype = { DATA, ACK, TIMER_EXPIRE };

/* Global state */
int logical_time = 0;
int segments_sent = 0;
int segments_acked = 0;
int acks_sent = 0;
int delayed_acks = 0;      /* Count of delayed ACKs */
int immediate_acks = 0;    /* Count of immediate ACKs */
int delayed_count = 0;     /* Segments received since last ACK (for LTL verification) */
bool connection_active = true;

/* Communication channels */
chan sender_to_receiver = [CHANNEL_SIZE] of { mtype, int };
chan receiver_to_sender = [CHANNEL_SIZE] of { mtype, int };
chan timer_chan = [1] of { mtype };

/* Sender process */
active proctype Sender() {
    int seq_num = 0;
    int expected_ack = 0;
    int ack_received;

    printf("Sender: Started (Default DACK)\n");

    do
    :: (seq_num < MAX_SEGMENTS && logical_time < MAX_TIME) ->
        atomic {
            sender_to_receiver ! DATA(seq_num);
            segments_sent++;
            printf("T=%d: Sender sent DATA seq=%d\n", logical_time, seq_num);
            seq_num++;
        }

    :: receiver_to_sender ? ACK(ack_received) ->
        atomic {
            assert(ack_received <= seq_num); /* ACK should not exceed sent */
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
    printf("Sender: Done. Sent=%d, Acked=%d, ACKs=%d\n",
           segments_sent, segments_acked, acks_sent);
}

/* Receiver process with Default DACK logic */
active proctype Receiver() {
    int expected_seq = 0;
    int received_seq;
    int last_ack_time = 0;      /* Time of last ACK */
    bool timer_pending = false; /* Is ACK timer active? */
    int timer_expiry = 0;       /* When timer expires */
    int last_acked_seq = -1;    /* Last acknowledged sequence */

    printf("Receiver: Started (Default DACK)\n");

    do
    :: sender_to_receiver ? DATA(received_seq) ->
        atomic {
            printf("T=%d: Receiver got DATA seq=%d (expected=%d)\n",
                   logical_time, received_seq, expected_seq);

            /* Check if out-of-order */
            if
            :: (received_seq != expected_seq) ->
                /* Out-of-order: immediate ACK */
                printf("T=%d: Out-of-order! Sending immediate ACK\n", logical_time);
                receiver_to_sender ! ACK(last_acked_seq);
                immediate_acks++;
                acks_sent++;
                delayed_count = 0;
                timer_pending = false;

            :: (received_seq == expected_seq) ->
                /* In-order segment */
                expected_seq++;
                delayed_count++;
                last_acked_seq = received_seq;

                if
                :: (delayed_count >= MAX_DELAYED_SEGS) ->
                    /* Reached max delayed segments: send ACK */
                    printf("T=%d: Max delayed segments reached, sending ACK=%d\n",
                           logical_time, received_seq);
                    receiver_to_sender ! ACK(received_seq);
                    delayed_acks++;
                    acks_sent++;
                    delayed_count = 0;
                    last_ack_time = logical_time;
                    timer_pending = false;

                :: (delayed_count < MAX_DELAYED_SEGS) ->
                    /* Set/reset timer */
                    if
                    :: (!timer_pending) ->
                        timer_expiry = logical_time + ACK_TIMEOUT;
                        timer_pending = true;
                        printf("T=%d: Timer set, expires at T=%d\n",
                               logical_time, timer_expiry);
                    :: (timer_pending) ->
                        /* Reset timer */
                        timer_expiry = logical_time + ACK_TIMEOUT;
                        printf("T=%d: Timer reset, expires at T=%d\n",
                               logical_time, timer_expiry);
                    fi
                fi
            fi
        }

    :: (timer_pending && logical_time >= timer_expiry) ->
        /* Timer expired: send ACK */
        atomic {
            printf("T=%d: Timer expired, sending ACK=%d\n",
                   logical_time, last_acked_seq);
            receiver_to_sender ! ACK(last_acked_seq);
            delayed_acks++;
            acks_sent++;
            delayed_count = 0;
            last_ack_time = logical_time;
            timer_pending = false;
        }

    :: (!connection_active && empty(sender_to_receiver) && !timer_pending) ->
        break;
    od

    printf("Receiver: Done. Immediate ACKs=%d, Delayed ACKs=%d\n",
           immediate_acks, delayed_acks);
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

/* LTL Properties for Default DACK */

/* S1: All segments eventually get acknowledged */
ltl eventual_ack_dack { <>(segments_sent > 0 -> segments_acked == segments_sent) }

/* S2: No more than 2 segments delayed before ACK */
ltl max_two_delayed { [](delayed_count <= MAX_DELAYED_SEGS) }

/* S3: ACKs are sent (system makes progress) */
ltl acks_sent_progress { []<>(acks_sent > 0) }

/* S4: Connection completes successfully */
ltl completion { <>(segments_sent == MAX_SEGMENTS && segments_acked == MAX_SEGMENTS) }
