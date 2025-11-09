/*
 * TCP Basic Model - Foundation for DACK and TCP-AAD verification
 *
 * This model implements a simple TCP sender-receiver interaction
 * with immediate acknowledgments (no delayed ACK logic).
 * Serves as baseline for verifying correctness properties.
 *
 * Time Abstraction: 1 logical time unit = 1ms (abstracted)
 */

#define MAX_SEGMENTS 5      /* Maximum number of segments to send */
#define CHANNEL_SIZE 10     /* Buffered channel size */

/* Message types */
mtype = { DATA, ACK };

/* Global variables */
int logical_time = 0;       /* Logical time counter */
int segments_sent = 0;      /* Total segments sent */
int segments_acked = 0;     /* Total segments acknowledged */
bool connection_active = true;

/* Communication channels */
chan sender_to_receiver = [CHANNEL_SIZE] of { mtype, int /* seq_num */ };
chan receiver_to_sender = [CHANNEL_SIZE] of { mtype, int /* ack_num */ };

/* Sender process */
active proctype Sender() {
    int seq_num = 0;
    int expected_ack = 0;
    int ack_received;

    printf("Sender: Started\n");

    do
    :: (seq_num < MAX_SEGMENTS) ->
        /* Send data segment */
        atomic {
            sender_to_receiver ! DATA(seq_num);
            segments_sent++;
            printf("Sender: Sent DATA seq=%d at time=%d\n", seq_num, logical_time);
            seq_num++;
        }

        /* Wait for ACK */
        receiver_to_sender ? ACK(ack_received);
        atomic {
            assert(ack_received == expected_ack); /* Verify ACK ordering */
            segments_acked++;
            expected_ack++;
            printf("Sender: Received ACK=%d at time=%d\n", ack_received, logical_time);
        }

    :: (seq_num >= MAX_SEGMENTS) ->
        break;
    od

    connection_active = false;
    printf("Sender: Completed. Sent=%d, Acked=%d\n", segments_sent, segments_acked);
}

/* Receiver process - Immediate ACK (no delay) */
active proctype Receiver() {
    int expected_seq = 0;
    int received_seq;

    printf("Receiver: Started\n");

    do
    :: sender_to_receiver ? DATA(received_seq) ->
        atomic {
            assert(received_seq == expected_seq); /* Verify in-order delivery */
            printf("Receiver: Received DATA seq=%d at time=%d\n", received_seq, logical_time);

            /* Send immediate ACK */
            receiver_to_sender ! ACK(received_seq);
            printf("Receiver: Sent ACK=%d at time=%d\n", received_seq, logical_time);

            expected_seq++;
        }

    :: (!connection_active && empty(sender_to_receiver)) ->
        break;
    od

    printf("Receiver: Completed\n");
}

/* Time keeper process */
active proctype TimeKeeper() {
    do
    :: atomic {
        logical_time++;
        /* Progress indication every 10 time units */
        if
        :: (logical_time % 10 == 0) ->
            printf("Time: %d\n", logical_time);
        :: else -> skip;
        fi
    }
    od
}

/* LTL Properties to verify */

/* Safety: All sent segments are eventually acknowledged */
ltl all_acked { <>(segments_sent == segments_acked && segments_sent == MAX_SEGMENTS) }

/* Safety: Segments sent equals segments acknowledged at completion */
ltl correct_count { []((!connection_active) -> (segments_sent == segments_acked)) }

/* Safety: No deadlock occurs */
ltl progress { []<>(segments_sent > 0 -> segments_acked > 0) }
