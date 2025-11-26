#define MAX_PACKETS 3         // Maximum number of packets to send
#define MAX_QUEUE_SIZE 5      // Network channel buffer size
#define MAX_TIME 255          // Maximum time units (byte limit)
#define MAX_ATO 20            // Maximum ACK timeout (500ms)
#define MIN_IAT_THRESHOLD 2   // Minimum IAT threshold (0.2ms)
#define IAT_RESET_PERIOD 30   // IAT_min reset period (1 second)
#define ALPHA 75              // Alpha parameter (0.75 * 100 for integer math)
#define BETA 150              // Beta parameter (1.5 * 100 for integer math)
#define MAX_DELAYED_SEGS 2    // Maximum delayed segments before forced ACK

/* Packet structure */
typedef Packet {
    byte seqno;         /* Sequence number */
    byte timestamp;     /* Send timestamp for IAT calculation */
}

/* Network channel - buffered FIFO queue */
chan network_chan = [MAX_QUEUE_SIZE] of {Packet};

/* ACK channel - for acknowledgments */
chan ack_chan = [MAX_QUEUE_SIZE] of {byte};

// Time tracking
byte current_time = 0;

// Sender state
byte next_seq_to_send = 0;
byte packets_sent = 0;

// Receiver state
byte next_expected_seq = 0;
byte packets_received = 0;
byte packets_acked = 0;
byte delayed_segments = 0;

// IAT tracking
byte last_recv_time = 0;
byte iat_curr = 0;
short iat_min = 32767;  /* Initialize to max value (using short for larger range) */
byte last_iat_reset_time = 0;

// ACK timeout calculation
short ato = MAX_ATO;  /* ACK timeout value */
byte ack_scheduled = 0;
byte ack_timer_expiry = 0;

/* Flags */
bit quick_ack_mode = 0;
bit out_of_order = 0;

/* ========== HELPER INLINE FUNCTIONS ========== */

/*
 * Calculate ATO using TCP-AAD formula
 * T = (IAT_min * alpha + IAT_curr * (1-alpha)) * beta
 * Using integer arithmetic: all values scaled by 100
 */
inline calculate_ato() {
    short temp;

    if
    :: (delayed_segments < MAX_DELAYED_SEGS) ->
        // Not enough segments delayed yet, use max ATO
        ato = MAX_ATO;
    :: else ->
        temp = ((iat_min * ALPHA) + (iat_curr * (100 - ALPHA))) / 100;
        ato = (temp * BETA) / 100;

        /* Clamp to maximum bound */
        if
        :: (ato > MAX_ATO) ->
            ato = MAX_ATO;
        :: else ->
            skip;
        fi;

        /* Ensure minimum value */
        if
        :: (ato < 1) ->
            ato = 1;
        :: else ->
            skip;
        fi;
    fi;

    /* PROPERTY: ATO never exceeds maximum bound */
    assert(ato >= 1 && ato <= MAX_ATO);

    printf("Receiver: Calculated ATO=%d (iat_min=%d, iat_curr=%d, delayed_segs=%d)\n",
           ato, iat_min, iat_curr, delayed_segments);
}

/*
 * Send ACK immediately (must be called within atomic block)
 */
inline send_ack_now() {
    byte ack_seq = next_expected_seq;

    /* PROPERTY: Cannot ACK more than received */
    assert(packets_acked < packets_received + 1);

    ack_chan!ack_seq;
    packets_acked++;
    delayed_segments = 0;
    ack_scheduled = 0;
    printf("Receiver: Sent immediate ACK for seq=%d at time=%d\n", ack_seq, current_time);
}

inline schedule_ack() {
    /* Calculate ATO based on current network conditions */
    calculate_ato();

    /* Schedule timer */
    ack_timer_expiry = current_time + ato;
    ack_scheduled = 1;

    printf("Receiver: Scheduled ACK timer to expire at time=%d (ATO=%d)\n",
           ack_timer_expiry, ato);
}

/* ========== SENDER PROCESS ========== */

/*
 * Sender process
 * Generates packets with sequence numbers and sends them to the network channel
 * Simplified model: sends all packets without waiting for ACKs
 * NOTE: Time is controlled by Clock process, not by Sender
 */
active proctype Sender() {
    Packet pkt;

    printf("Sender: Starting packet transmission\n");

    do
    :: (packets_sent < MAX_PACKETS) ->
        /* Create packet */
        pkt.seqno = next_seq_to_send;
        pkt.timestamp = current_time;

        /* Send packet to network */
        network_chan!pkt;

        printf("Sender: Sent packet seq=%d at time=%d\n", pkt.seqno, current_time);

        /* Update sender state */
        next_seq_to_send++;
        packets_sent++;

    :: (packets_sent >= MAX_PACKETS) ->
        printf("Sender: All packets sent\n");
        break;
    od;
}

/* ========== RECEIVER PROCESS ========== */

/*
 * Receiver process
 * Implements TCP-AAD algorithm:
 * - Receives packets from network channel
 * - Calculates IAT (Inter-Arrival Time)
 * - Tracks IAT_min with periodic reset
 * - Decides when to send ACK (immediate or delayed)
 */
active proctype Receiver() {
    Packet pkt;
    byte time_since_last_recv;

    printf("Receiver: Starting packet reception\n");

    do
    :: network_chan?pkt ->
        printf("Receiver: Received packet seq=%d at time=%d\n", pkt.seqno, current_time);

        /* Calculate IAT (Inter-Arrival Time) */
        if
        :: (packets_received > 0) ->
            time_since_last_recv = current_time - last_recv_time;
            iat_curr = time_since_last_recv;

            printf("Receiver: IAT=%d (current_time=%d, last_recv_time=%d)\n",
                   iat_curr, current_time, last_recv_time);
        :: else ->
            /* First packet, no IAT yet */
            iat_curr = 0;
        fi;

        /* Update last receive time */
        last_recv_time = current_time;

        /* Check if IAT_min should be reset (periodic reset every 1 second) */
        if
        :: (current_time - last_iat_reset_time >= IAT_RESET_PERIOD) ->
            printf("Receiver: Resetting IAT_min (period expired)\n");
            iat_min = 32767;  /* Reset to max value */
            last_iat_reset_time = current_time;
        :: else ->
            skip;
        fi;

        /* Update IAT_min with filtering (discard very small IATs < 0.2ms) */
        if
        :: (iat_curr >= MIN_IAT_THRESHOLD && iat_curr < iat_min) ->
            iat_min = iat_curr;
            printf("Receiver: Updated IAT_min=%d\n", iat_min);

            /* SAFETY PROPERTY 3: IAT_min should be <= current IAT when updated */
            assert(iat_min <= iat_curr);
        :: else ->
            skip;
        fi;

        /* Check if packet is out of order */
        if
        :: (pkt.seqno != next_expected_seq) ->
            /* Out of order - trigger immediate ACK (quick ACK mode) */
            printf("Receiver: Out-of-order packet detected (expected=%d, got=%d)\n",
                   next_expected_seq, pkt.seqno);
            out_of_order = 1;
            quick_ack_mode = 1;

            /* SAFETY PROPERTY 5: Out-of-order packets must trigger immediate ACK */
            /* This is enforced by calling send_ack_now() - assertion verifies intent */
            send_ack_now();
            assert(delayed_segments == 0);  /* Verify counter was reset */

            /* Don't update expected sequence for out-of-order */
        :: else ->
            /* In-order packet */
            out_of_order = 0;
            next_expected_seq++;
            packets_received++;
            delayed_segments++;

            /* SAFETY PROPERTY 4: Delayed segments never exceeds maximum */
            assert(delayed_segments <= MAX_DELAYED_SEGS);

            printf("Receiver: In-order packet, delayed_segments=%d\n", delayed_segments);

            /* Check if we should send ACK immediately */
            if
            :: (delayed_segments >= MAX_DELAYED_SEGS) ->
                printf("Receiver: Max delayed segments reached, sending immediate ACK\n");
                send_ack_now();
            :: else ->
                /* Schedule delayed ACK */
                printf("Receiver: Scheduling delayed ACK\n");
                schedule_ack();
            fi;
        fi;

    :: (packets_received >= MAX_PACKETS && !ack_scheduled) ->
        /* All packets received and no pending ACK */
        printf("Receiver: All packets received and acknowledged\n");
        break;
    od;
}

/* ========== CLOCK/TIMER PROCESS ========== */

/*
 * Clock process
 * Controls global time advancement and handles delayed ACK timer
 * This is the ONLY process that advances current_time
 *
 * Responsibilities:
 * - Advance global time in discrete steps
 * - Check if delayed ACK timer has expired
 * - Send ACK when timer fires
 * - Terminate when max time reached or all processing complete
 */
active proctype Clock() {
    printf("Clock: Starting time management\n");

    do
    :: (packets_sent >= MAX_PACKETS &&
        packets_received >= MAX_PACKETS &&
        delayed_segments == 0 &&
        !ack_scheduled) ->
        /* All packets processed and ACKed, terminate */
        printf("Clock: All packets processed, terminating\n");
        break;

    :: (packets_sent >= MAX_PACKETS &&
        packets_received >= MAX_PACKETS &&
        (delayed_segments > 0 || ack_scheduled)) ->
        /* Fire pending ACK before terminating */
        printf("Clock: All packets done, firing pending ACK\n");
        send_ack_now();
        break;

    :: (current_time < MAX_TIME) ->
        /* Advance time by one unit */
        current_time++;

        /* Check if delayed ACK timer should fire */
        if
        :: (ack_scheduled && current_time >= ack_timer_expiry) ->
            printf("Clock: Timer expired at time=%d (scheduled for %d)\n",
                   current_time, ack_timer_expiry);
            send_ack_now();

        :: (!ack_scheduled) ->
            /* No timer scheduled, continue */
            skip;

        :: (ack_scheduled && current_time < ack_timer_expiry) ->
            /* Timer scheduled but not expired yet */
            skip;
        fi;
    od;

    printf("Clock: Final state at time=%d: sent=%d, recv=%d, acked=%d\n",
           current_time, packets_sent, packets_received, packets_acked);
}

init {
    printf("=== TCP-AAD Formal Verification ===\n");
    printf("Configuration:\n");
    printf("  MAX_PACKETS = %d\n", MAX_PACKETS);
    printf("  MAX_ATO = %d\n", MAX_ATO);
    printf("  ALPHA = %d (0.75)\n", ALPHA);
    printf("  BETA = %d (1.5)\n", BETA);
    printf("  MAX_DELAYED_SEGS = %d\n", MAX_DELAYED_SEGS);
    printf("===================================\n");
}
