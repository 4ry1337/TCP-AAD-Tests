	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */
;
		
	case 3: // STATE 1
		goto R999;

	case 4: // STATE 9
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Clock */
;
		;
		;
		;
		;
		;
		;
		;
		;
		;
		
	case 10: // STATE 7
		;
		((P2 *)_this)->_6_4_ack_seq = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 12: // STATE 9
		;
		_m = unsend(now.ack_chan);
		;
		goto R999;

	case 13: // STATE 10
		;
		now.packets_acked = trpt->bup.oval;
		;
		goto R999;

	case 14: // STATE 11
		;
		now.delayed_segments = trpt->bup.oval;
		;
		goto R999;

	case 15: // STATE 12
		;
		now.ack_scheduled = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 18: // STATE 17
		;
		now.current_time = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 21: // STATE 20
		;
		((P2 *)_this)->_6_5_ack_seq = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 23: // STATE 22
		;
		_m = unsend(now.ack_chan);
		;
		goto R999;

	case 24: // STATE 23
		;
		now.packets_acked = trpt->bup.oval;
		;
		goto R999;

	case 25: // STATE 24
		;
		now.delayed_segments = trpt->bup.oval;
		;
		goto R999;

	case 26: // STATE 25
		;
		now.ack_scheduled = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		;
		;
		;
		;
		
	case 31: // STATE 38
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Receiver */
;
		;
		
	case 33: // STATE 2
		;
		XX = 1;
		unrecv(now.network_chan, XX-1, 0, ((int)((P1 *)_this)->pkt.seqno), 1);
		unrecv(now.network_chan, XX-1, 1, ((int)((P1 *)_this)->pkt.timestamp), 0);
		((P1 *)_this)->pkt.seqno = trpt->bup.ovals[0];
		((P1 *)_this)->pkt.timestamp = trpt->bup.ovals[1];
		;
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;
;
		;
		;
		;
		
	case 36: // STATE 5
		;
		((P1 *)_this)->time_since_last_recv = trpt->bup.oval;
		;
		goto R999;

	case 37: // STATE 6
		;
		now.iat_curr = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 39: // STATE 9
		;
		now.iat_curr = trpt->bup.oval;
		;
		goto R999;

	case 40: // STATE 12
		;
		now.last_recv_time = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 43: // STATE 15
		;
		now.iat_min = trpt->bup.oval;
		;
		goto R999;

	case 44: // STATE 16
		;
		now.last_iat_reset_time = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 46: // STATE 22
		;
		now.iat_min = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		;
		;
		;
		;
		
	case 51: // STATE 31
		;
		out_of_order = trpt->bup.oval;
		;
		goto R999;

	case 52: // STATE 32
		;
		quick_ack_mode = trpt->bup.oval;
		;
		goto R999;

	case 53: // STATE 33
		;
		((P1 *)_this)->_5_1_ack_seq = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 55: // STATE 35
		;
		_m = unsend(now.ack_chan);
		;
		goto R999;

	case 56: // STATE 36
		;
		now.packets_acked = trpt->bup.oval;
		;
		goto R999;

	case 57: // STATE 37
		;
		now.delayed_segments = trpt->bup.oval;
		;
		goto R999;

	case 58: // STATE 38
		;
		now.ack_scheduled = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 61: // STATE 43
		;
		out_of_order = trpt->bup.oval;
		;
		goto R999;

	case 62: // STATE 44
		;
		now.next_expected_seq = trpt->bup.oval;
		;
		goto R999;

	case 63: // STATE 45
		;
		now.packets_received = trpt->bup.oval;
		;
		goto R999;

	case 64: // STATE 46
		;
		now.delayed_segments = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		;
		;
		;
		;
		
	case 69: // STATE 51
		;
		((P1 *)_this)->_5_2_ack_seq = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 71: // STATE 53
		;
		_m = unsend(now.ack_chan);
		;
		goto R999;

	case 72: // STATE 54
		;
		now.packets_acked = trpt->bup.oval;
		;
		goto R999;

	case 73: // STATE 55
		;
		now.delayed_segments = trpt->bup.oval;
		;
		goto R999;

	case 74: // STATE 56
		;
		now.ack_scheduled = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 77: // STATE 61
		;
		((P1 *)_this)->_5_3_1_temp = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 79: // STATE 63
		;
		now.ato = trpt->bup.oval;
		;
		goto R999;

	case 80: // STATE 65
		;
		((P1 *)_this)->_5_3_1_temp = trpt->bup.oval;
		;
		goto R999;

	case 81: // STATE 66
		;
		now.ato = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 83: // STATE 68
		;
		now.ato = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 85: // STATE 74
		;
		now.ato = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 88: // STATE 84
		;
		now.ack_timer_expiry = trpt->bup.oval;
		;
		goto R999;

	case 89: // STATE 85
		;
		now.ack_scheduled = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		;
		;
		
	case 93: // STATE 98
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Sender */
;
		;
		;
		;
		
	case 96: // STATE 3
		;
		((P0 *)_this)->pkt.seqno = trpt->bup.oval;
		;
		goto R999;

	case 97: // STATE 4
		;
		((P0 *)_this)->pkt.timestamp = trpt->bup.oval;
		;
		goto R999;

	case 98: // STATE 5
		;
		_m = unsend(now.network_chan);
		;
		goto R999;
;
		;
		
	case 100: // STATE 7
		;
		now.next_seq_to_send = trpt->bup.oval;
		;
		goto R999;

	case 101: // STATE 8
		;
		now.packets_sent = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 104: // STATE 15
		;
		p_restor(II);
		;
		;
		goto R999;
	}

