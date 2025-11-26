#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC :init: */
	case 3: // STATE 1 - tcp_aad.pml:349 - [printf('=== TCP-AAD Formal Verification ===\\n')] (0:9:0 - 1)
		IfNotBlocked
		reached[3][1] = 1;
		Printf("=== TCP-AAD Formal Verification ===\n");
		/* merge: printf('Configuration:\\n')(9, 2, 9) */
		reached[3][2] = 1;
		Printf("Configuration:\n");
		/* merge: printf('  MAX_PACKETS = %d\\n',3)(9, 3, 9) */
		reached[3][3] = 1;
		Printf("  MAX_PACKETS = %d\n", 3);
		/* merge: printf('  MAX_ATO = %d\\n',20)(9, 4, 9) */
		reached[3][4] = 1;
		Printf("  MAX_ATO = %d\n", 20);
		/* merge: printf('  ALPHA = %d (0.75)\\n',75)(9, 5, 9) */
		reached[3][5] = 1;
		Printf("  ALPHA = %d (0.75)\n", 75);
		/* merge: printf('  BETA = %d (1.5)\\n',150)(9, 6, 9) */
		reached[3][6] = 1;
		Printf("  BETA = %d (1.5)\n", 150);
		/* merge: printf('  MAX_DELAYED_SEGS = %d\\n',2)(9, 7, 9) */
		reached[3][7] = 1;
		Printf("  MAX_DELAYED_SEGS = %d\n", 2);
		/* merge: printf('===================================\\n')(9, 8, 9) */
		reached[3][8] = 1;
		Printf("===================================\n");
		_m = 3; goto P999; /* 7 */
	case 4: // STATE 9 - tcp_aad.pml:360 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[3][9] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Clock */
	case 5: // STATE 1 - tcp_aad.pml:299 - [printf('Clock: Starting time management\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[2][1] = 1;
		Printf("Clock: Starting time management\n");
		_m = 3; goto P999; /* 0 */
	case 6: // STATE 2 - tcp_aad.pml:305 - [(((((packets_sent>=3)&&(packets_received>=3))&&(delayed_segments==0))&&!(ack_scheduled)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][2] = 1;
		if (!(((((((int)now.packets_sent)>=3)&&(((int)now.packets_received)>=3))&&(((int)now.delayed_segments)==0))&& !(((int)now.ack_scheduled)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 3 - tcp_aad.pml:307 - [printf('Clock: All packets processed, terminating\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[2][3] = 1;
		Printf("Clock: All packets processed, terminating\n");
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 5 - tcp_aad.pml:312 - [((((packets_sent>=3)&&(packets_received>=3))&&((delayed_segments>0)||ack_scheduled)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][5] = 1;
		if (!((((((int)now.packets_sent)>=3)&&(((int)now.packets_received)>=3))&&((((int)now.delayed_segments)>0)||((int)now.ack_scheduled)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 6 - tcp_aad.pml:314 - [printf('Clock: All packets done, firing pending ACK\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[2][6] = 1;
		Printf("Clock: All packets done, firing pending ACK\n");
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 7 - tcp_aad.pml:117 - [ack_seq = next_expected_seq] (0:0:1 - 1)
		IfNotBlocked
		reached[2][7] = 1;
		(trpt+1)->bup.oval = ((int)((P2 *)_this)->_6_4_ack_seq);
		((P2 *)_this)->_6_4_ack_seq = ((int)now.next_expected_seq);
#ifdef VAR_RANGES
		logval("Clock:ack_seq", ((int)((P2 *)_this)->_6_4_ack_seq));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 8 - tcp_aad.pml:117 - [assert((packets_acked<(packets_received+1)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][8] = 1;
		spin_assert((((int)now.packets_acked)<(((int)now.packets_received)+1)), "(packets_acked<(packets_received+1))", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 9 - tcp_aad.pml:120 - [ack_chan!ack_seq] (0:0:0 - 1)
		IfNotBlocked
		reached[2][9] = 1;
		if (q_full(now.ack_chan))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[64];
			sprintf(simvals, "%d!", now.ack_chan);
		sprintf(simtmp, "%d", ((int)((P2 *)_this)->_6_4_ack_seq)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.ack_chan, 0, ((int)((P2 *)_this)->_6_4_ack_seq), 0, 1);
		_m = 2; goto P999; /* 0 */
	case 13: // STATE 10 - tcp_aad.pml:121 - [packets_acked = (packets_acked+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[2][10] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_acked);
		now.packets_acked = (((int)now.packets_acked)+1);
#ifdef VAR_RANGES
		logval("packets_acked", ((int)now.packets_acked));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 11 - tcp_aad.pml:124 - [delayed_segments = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[2][11] = 1;
		(trpt+1)->bup.oval = ((int)now.delayed_segments);
		now.delayed_segments = 0;
#ifdef VAR_RANGES
		logval("delayed_segments", ((int)now.delayed_segments));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 12 - tcp_aad.pml:127 - [ack_scheduled = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[2][12] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_scheduled);
		now.ack_scheduled = 0;
#ifdef VAR_RANGES
		logval("ack_scheduled", ((int)now.ack_scheduled));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 13 - tcp_aad.pml:129 - [printf('Receiver: Sent immediate ACK for seq=%d at time=%d\\n',ack_seq,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[2][13] = 1;
		Printf("Receiver: Sent immediate ACK for seq=%d at time=%d\n", ((int)((P2 *)_this)->_6_4_ack_seq), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 16 - tcp_aad.pml:318 - [((current_time<255))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][16] = 1;
		if (!((((int)now.current_time)<255)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 17 - tcp_aad.pml:320 - [current_time = (current_time+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[2][17] = 1;
		(trpt+1)->bup.oval = ((int)now.current_time);
		now.current_time = (((int)now.current_time)+1);
#ifdef VAR_RANGES
		logval("current_time", ((int)now.current_time));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 19: // STATE 18 - tcp_aad.pml:324 - [((ack_scheduled&&(current_time>=ack_timer_expiry)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][18] = 1;
		if (!((((int)now.ack_scheduled)&&(((int)now.current_time)>=((int)now.ack_timer_expiry)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 19 - tcp_aad.pml:325 - [printf('Clock: Timer expired at time=%d (scheduled for %d)\\n',current_time,ack_timer_expiry)] (0:0:0 - 1)
		IfNotBlocked
		reached[2][19] = 1;
		Printf("Clock: Timer expired at time=%d (scheduled for %d)\n", ((int)now.current_time), ((int)now.ack_timer_expiry));
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 20 - tcp_aad.pml:117 - [ack_seq = next_expected_seq] (0:0:1 - 1)
		IfNotBlocked
		reached[2][20] = 1;
		(trpt+1)->bup.oval = ((int)((P2 *)_this)->_6_5_ack_seq);
		((P2 *)_this)->_6_5_ack_seq = ((int)now.next_expected_seq);
#ifdef VAR_RANGES
		logval("Clock:ack_seq", ((int)((P2 *)_this)->_6_5_ack_seq));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 21 - tcp_aad.pml:117 - [assert((packets_acked<(packets_received+1)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][21] = 1;
		spin_assert((((int)now.packets_acked)<(((int)now.packets_received)+1)), "(packets_acked<(packets_received+1))", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 22 - tcp_aad.pml:120 - [ack_chan!ack_seq] (0:0:0 - 1)
		IfNotBlocked
		reached[2][22] = 1;
		if (q_full(now.ack_chan))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[64];
			sprintf(simvals, "%d!", now.ack_chan);
		sprintf(simtmp, "%d", ((int)((P2 *)_this)->_6_5_ack_seq)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.ack_chan, 0, ((int)((P2 *)_this)->_6_5_ack_seq), 0, 1);
		_m = 2; goto P999; /* 0 */
	case 24: // STATE 23 - tcp_aad.pml:121 - [packets_acked = (packets_acked+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[2][23] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_acked);
		now.packets_acked = (((int)now.packets_acked)+1);
#ifdef VAR_RANGES
		logval("packets_acked", ((int)now.packets_acked));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 25: // STATE 24 - tcp_aad.pml:124 - [delayed_segments = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[2][24] = 1;
		(trpt+1)->bup.oval = ((int)now.delayed_segments);
		now.delayed_segments = 0;
#ifdef VAR_RANGES
		logval("delayed_segments", ((int)now.delayed_segments));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 26: // STATE 25 - tcp_aad.pml:127 - [ack_scheduled = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[2][25] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_scheduled);
		now.ack_scheduled = 0;
#ifdef VAR_RANGES
		logval("ack_scheduled", ((int)now.ack_scheduled));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 27: // STATE 26 - tcp_aad.pml:129 - [printf('Receiver: Sent immediate ACK for seq=%d at time=%d\\n',ack_seq,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[2][26] = 1;
		Printf("Receiver: Sent immediate ACK for seq=%d at time=%d\n", ((int)((P2 *)_this)->_6_5_ack_seq), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 28: // STATE 28 - tcp_aad.pml:329 - [(!(ack_scheduled))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][28] = 1;
		if (!( !(((int)now.ack_scheduled))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 29: // STATE 30 - tcp_aad.pml:333 - [((ack_scheduled&&(current_time<ack_timer_expiry)))] (0:0:0 - 1)
		IfNotBlocked
		reached[2][30] = 1;
		if (!((((int)now.ack_scheduled)&&(((int)now.current_time)<((int)now.ack_timer_expiry)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 30: // STATE 37 - tcp_aad.pml:339 - [printf('Clock: Final state at time=%d: sent=%d, recv=%d, acked=%d\\n',current_time,packets_sent,packets_received,packets_acked)] (0:0:0 - 5)
		IfNotBlocked
		reached[2][37] = 1;
		Printf("Clock: Final state at time=%d: sent=%d, recv=%d, acked=%d\n", ((int)now.current_time), ((int)now.packets_sent), ((int)now.packets_received), ((int)now.packets_acked));
		_m = 3; goto P999; /* 0 */
	case 31: // STATE 38 - tcp_aad.pml:341 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[2][38] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Receiver */
	case 32: // STATE 1 - tcp_aad.pml:195 - [printf('Receiver: Starting packet reception\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		Printf("Receiver: Starting packet reception\n");
		_m = 3; goto P999; /* 0 */
	case 33: // STATE 2 - tcp_aad.pml:198 - [network_chan?pkt.seqno,pkt.timestamp] (0:0:2 - 1)
		reached[1][2] = 1;
		if (q_len(now.network_chan) == 0) continue;

		XX=1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((int)((P1 *)_this)->pkt.seqno);
		(trpt+1)->bup.ovals[1] = ((int)((P1 *)_this)->pkt.timestamp);
		;
		((P1 *)_this)->pkt.seqno = qrecv(now.network_chan, XX-1, 0, 0);
#ifdef VAR_RANGES
		logval("Receiver:pkt.seqno", ((int)((P1 *)_this)->pkt.seqno));
#endif
		;
		((P1 *)_this)->pkt.timestamp = qrecv(now.network_chan, XX-1, 1, 1);
#ifdef VAR_RANGES
		logval("Receiver:pkt.timestamp", ((int)((P1 *)_this)->pkt.timestamp));
#endif
		;
		
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d?", now.network_chan);
		sprintf(simtmp, "%d", ((int)((P1 *)_this)->pkt.seqno)); strcat(simvals, simtmp);		strcat(simvals, ",");
		sprintf(simtmp, "%d", ((int)((P1 *)_this)->pkt.timestamp)); strcat(simvals, simtmp);		}
#endif
		;
		_m = 4; goto P999; /* 0 */
	case 34: // STATE 3 - tcp_aad.pml:199 - [printf('Receiver: Received packet seq=%d at time=%d\\n',pkt.seqno,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		Printf("Receiver: Received packet seq=%d at time=%d\n", ((int)((P1 *)_this)->pkt.seqno), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 35: // STATE 4 - tcp_aad.pml:203 - [((packets_received>0))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		if (!((((int)now.packets_received)>0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 36: // STATE 5 - tcp_aad.pml:204 - [time_since_last_recv = (current_time-last_recv_time)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][5] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->time_since_last_recv);
		((P1 *)_this)->time_since_last_recv = (((int)now.current_time)-((int)now.last_recv_time));
#ifdef VAR_RANGES
		logval("Receiver:time_since_last_recv", ((int)((P1 *)_this)->time_since_last_recv));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 37: // STATE 6 - tcp_aad.pml:205 - [iat_curr = time_since_last_recv] (0:0:1 - 1)
		IfNotBlocked
		reached[1][6] = 1;
		(trpt+1)->bup.oval = ((int)now.iat_curr);
		now.iat_curr = ((int)((P1 *)_this)->time_since_last_recv);
#ifdef VAR_RANGES
		logval("iat_curr", ((int)now.iat_curr));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 38: // STATE 7 - tcp_aad.pml:207 - [printf('Receiver: IAT=%d (current_time=%d, last_recv_time=%d)\\n',iat_curr,current_time,last_recv_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][7] = 1;
		Printf("Receiver: IAT=%d (current_time=%d, last_recv_time=%d)\n", ((int)now.iat_curr), ((int)now.current_time), ((int)now.last_recv_time));
		_m = 3; goto P999; /* 0 */
	case 39: // STATE 9 - tcp_aad.pml:211 - [iat_curr = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][9] = 1;
		(trpt+1)->bup.oval = ((int)now.iat_curr);
		now.iat_curr = 0;
#ifdef VAR_RANGES
		logval("iat_curr", ((int)now.iat_curr));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 40: // STATE 12 - tcp_aad.pml:215 - [last_recv_time = current_time] (0:0:1 - 3)
		IfNotBlocked
		reached[1][12] = 1;
		(trpt+1)->bup.oval = ((int)now.last_recv_time);
		now.last_recv_time = ((int)now.current_time);
#ifdef VAR_RANGES
		logval("last_recv_time", ((int)now.last_recv_time));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 41: // STATE 13 - tcp_aad.pml:219 - [(((current_time-last_iat_reset_time)>=30))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][13] = 1;
		if (!(((((int)now.current_time)-((int)now.last_iat_reset_time))>=30)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 42: // STATE 14 - tcp_aad.pml:220 - [printf('Receiver: Resetting IAT_min (period expired)\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[1][14] = 1;
		Printf("Receiver: Resetting IAT_min (period expired)\n");
		_m = 3; goto P999; /* 0 */
	case 43: // STATE 15 - tcp_aad.pml:221 - [iat_min = 32767] (0:0:1 - 1)
		IfNotBlocked
		reached[1][15] = 1;
		(trpt+1)->bup.oval = now.iat_min;
		now.iat_min = 32767;
#ifdef VAR_RANGES
		logval("iat_min", now.iat_min);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 44: // STATE 16 - tcp_aad.pml:222 - [last_iat_reset_time = current_time] (0:0:1 - 1)
		IfNotBlocked
		reached[1][16] = 1;
		(trpt+1)->bup.oval = ((int)now.last_iat_reset_time);
		now.last_iat_reset_time = ((int)now.current_time);
#ifdef VAR_RANGES
		logval("last_iat_reset_time", ((int)now.last_iat_reset_time));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 45: // STATE 21 - tcp_aad.pml:229 - [(((iat_curr>=2)&&(iat_curr<iat_min)))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][21] = 1;
		if (!(((((int)now.iat_curr)>=2)&&(((int)now.iat_curr)<now.iat_min))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 46: // STATE 22 - tcp_aad.pml:230 - [iat_min = iat_curr] (0:0:1 - 1)
		IfNotBlocked
		reached[1][22] = 1;
		(trpt+1)->bup.oval = now.iat_min;
		now.iat_min = ((int)now.iat_curr);
#ifdef VAR_RANGES
		logval("iat_min", now.iat_min);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 47: // STATE 23 - tcp_aad.pml:231 - [printf('Receiver: Updated IAT_min=%d\\n',iat_min)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][23] = 1;
		Printf("Receiver: Updated IAT_min=%d\n", now.iat_min);
		_m = 3; goto P999; /* 0 */
	case 48: // STATE 24 - tcp_aad.pml:234 - [assert((iat_min<=iat_curr))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][24] = 1;
		spin_assert((now.iat_min<=((int)now.iat_curr)), "(iat_min<=iat_curr)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 49: // STATE 29 - tcp_aad.pml:241 - [((pkt.seqno!=next_expected_seq))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][29] = 1;
		if (!((((int)((P1 *)_this)->pkt.seqno)!=((int)now.next_expected_seq))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 50: // STATE 30 - tcp_aad.pml:243 - [printf('Receiver: Out-of-order packet detected (expected=%d, got=%d)\\n',next_expected_seq,pkt.seqno)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][30] = 1;
		Printf("Receiver: Out-of-order packet detected (expected=%d, got=%d)\n", ((int)now.next_expected_seq), ((int)((P1 *)_this)->pkt.seqno));
		_m = 3; goto P999; /* 0 */
	case 51: // STATE 31 - tcp_aad.pml:245 - [out_of_order = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][31] = 1;
		(trpt+1)->bup.oval = ((int)out_of_order);
		out_of_order = 1;
#ifdef VAR_RANGES
		logval("out_of_order", ((int)out_of_order));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 52: // STATE 32 - tcp_aad.pml:246 - [quick_ack_mode = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][32] = 1;
		(trpt+1)->bup.oval = ((int)quick_ack_mode);
		quick_ack_mode = 1;
#ifdef VAR_RANGES
		logval("quick_ack_mode", ((int)quick_ack_mode));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 53: // STATE 33 - tcp_aad.pml:117 - [ack_seq = next_expected_seq] (0:0:1 - 1)
		IfNotBlocked
		reached[1][33] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->_5_1_ack_seq);
		((P1 *)_this)->_5_1_ack_seq = ((int)now.next_expected_seq);
#ifdef VAR_RANGES
		logval("Receiver:ack_seq", ((int)((P1 *)_this)->_5_1_ack_seq));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 54: // STATE 34 - tcp_aad.pml:117 - [assert((packets_acked<(packets_received+1)))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][34] = 1;
		spin_assert((((int)now.packets_acked)<(((int)now.packets_received)+1)), "(packets_acked<(packets_received+1))", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 55: // STATE 35 - tcp_aad.pml:120 - [ack_chan!ack_seq] (0:0:0 - 1)
		IfNotBlocked
		reached[1][35] = 1;
		if (q_full(now.ack_chan))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[64];
			sprintf(simvals, "%d!", now.ack_chan);
		sprintf(simtmp, "%d", ((int)((P1 *)_this)->_5_1_ack_seq)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.ack_chan, 0, ((int)((P1 *)_this)->_5_1_ack_seq), 0, 1);
		_m = 2; goto P999; /* 0 */
	case 56: // STATE 36 - tcp_aad.pml:121 - [packets_acked = (packets_acked+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][36] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_acked);
		now.packets_acked = (((int)now.packets_acked)+1);
#ifdef VAR_RANGES
		logval("packets_acked", ((int)now.packets_acked));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 57: // STATE 37 - tcp_aad.pml:124 - [delayed_segments = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][37] = 1;
		(trpt+1)->bup.oval = ((int)now.delayed_segments);
		now.delayed_segments = 0;
#ifdef VAR_RANGES
		logval("delayed_segments", ((int)now.delayed_segments));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 58: // STATE 38 - tcp_aad.pml:127 - [ack_scheduled = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][38] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_scheduled);
		now.ack_scheduled = 0;
#ifdef VAR_RANGES
		logval("ack_scheduled", ((int)now.ack_scheduled));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 59: // STATE 39 - tcp_aad.pml:129 - [printf('Receiver: Sent immediate ACK for seq=%d at time=%d\\n',ack_seq,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][39] = 1;
		Printf("Receiver: Sent immediate ACK for seq=%d at time=%d\n", ((int)((P1 *)_this)->_5_1_ack_seq), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 60: // STATE 41 - tcp_aad.pml:251 - [assert((delayed_segments==0))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][41] = 1;
		spin_assert((((int)now.delayed_segments)==0), "(delayed_segments==0)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 61: // STATE 43 - tcp_aad.pml:256 - [out_of_order = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][43] = 1;
		(trpt+1)->bup.oval = ((int)out_of_order);
		out_of_order = 0;
#ifdef VAR_RANGES
		logval("out_of_order", ((int)out_of_order));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 62: // STATE 44 - tcp_aad.pml:257 - [next_expected_seq = (next_expected_seq+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][44] = 1;
		(trpt+1)->bup.oval = ((int)now.next_expected_seq);
		now.next_expected_seq = (((int)now.next_expected_seq)+1);
#ifdef VAR_RANGES
		logval("next_expected_seq", ((int)now.next_expected_seq));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 63: // STATE 45 - tcp_aad.pml:258 - [packets_received = (packets_received+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][45] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_received);
		now.packets_received = (((int)now.packets_received)+1);
#ifdef VAR_RANGES
		logval("packets_received", ((int)now.packets_received));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 64: // STATE 46 - tcp_aad.pml:259 - [delayed_segments = (delayed_segments+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][46] = 1;
		(trpt+1)->bup.oval = ((int)now.delayed_segments);
		now.delayed_segments = (((int)now.delayed_segments)+1);
#ifdef VAR_RANGES
		logval("delayed_segments", ((int)now.delayed_segments));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 65: // STATE 47 - tcp_aad.pml:262 - [assert((delayed_segments<=2))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][47] = 1;
		spin_assert((((int)now.delayed_segments)<=2), "(delayed_segments<=2)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 66: // STATE 48 - tcp_aad.pml:264 - [printf('Receiver: In-order packet, delayed_segments=%d\\n',delayed_segments)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][48] = 1;
		Printf("Receiver: In-order packet, delayed_segments=%d\n", ((int)now.delayed_segments));
		_m = 3; goto P999; /* 0 */
	case 67: // STATE 49 - tcp_aad.pml:268 - [((delayed_segments>=2))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][49] = 1;
		if (!((((int)now.delayed_segments)>=2)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 68: // STATE 50 - tcp_aad.pml:269 - [printf('Receiver: Max delayed segments reached, sending immediate ACK\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[1][50] = 1;
		Printf("Receiver: Max delayed segments reached, sending immediate ACK\n");
		_m = 3; goto P999; /* 0 */
	case 69: // STATE 51 - tcp_aad.pml:117 - [ack_seq = next_expected_seq] (0:0:1 - 1)
		IfNotBlocked
		reached[1][51] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->_5_2_ack_seq);
		((P1 *)_this)->_5_2_ack_seq = ((int)now.next_expected_seq);
#ifdef VAR_RANGES
		logval("Receiver:ack_seq", ((int)((P1 *)_this)->_5_2_ack_seq));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 70: // STATE 52 - tcp_aad.pml:117 - [assert((packets_acked<(packets_received+1)))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][52] = 1;
		spin_assert((((int)now.packets_acked)<(((int)now.packets_received)+1)), "(packets_acked<(packets_received+1))", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 71: // STATE 53 - tcp_aad.pml:120 - [ack_chan!ack_seq] (0:0:0 - 1)
		IfNotBlocked
		reached[1][53] = 1;
		if (q_full(now.ack_chan))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[64];
			sprintf(simvals, "%d!", now.ack_chan);
		sprintf(simtmp, "%d", ((int)((P1 *)_this)->_5_2_ack_seq)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.ack_chan, 0, ((int)((P1 *)_this)->_5_2_ack_seq), 0, 1);
		_m = 2; goto P999; /* 0 */
	case 72: // STATE 54 - tcp_aad.pml:121 - [packets_acked = (packets_acked+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][54] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_acked);
		now.packets_acked = (((int)now.packets_acked)+1);
#ifdef VAR_RANGES
		logval("packets_acked", ((int)now.packets_acked));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 73: // STATE 55 - tcp_aad.pml:124 - [delayed_segments = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][55] = 1;
		(trpt+1)->bup.oval = ((int)now.delayed_segments);
		now.delayed_segments = 0;
#ifdef VAR_RANGES
		logval("delayed_segments", ((int)now.delayed_segments));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 74: // STATE 56 - tcp_aad.pml:127 - [ack_scheduled = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][56] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_scheduled);
		now.ack_scheduled = 0;
#ifdef VAR_RANGES
		logval("ack_scheduled", ((int)now.ack_scheduled));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 75: // STATE 57 - tcp_aad.pml:129 - [printf('Receiver: Sent immediate ACK for seq=%d at time=%d\\n',ack_seq,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][57] = 1;
		Printf("Receiver: Sent immediate ACK for seq=%d at time=%d\n", ((int)((P1 *)_this)->_5_2_ack_seq), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 76: // STATE 60 - tcp_aad.pml:273 - [printf('Receiver: Scheduling delayed ACK\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[1][60] = 1;
		Printf("Receiver: Scheduling delayed ACK\n");
		_m = 3; goto P999; /* 0 */
	case 77: // STATE 61 - tcp_aad.pml:76 - [temp = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][61] = 1;
		(trpt+1)->bup.oval = ((P1 *)_this)->_5_3_1_temp;
		((P1 *)_this)->_5_3_1_temp = 0;
#ifdef VAR_RANGES
		logval("Receiver:temp", ((P1 *)_this)->_5_3_1_temp);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 78: // STATE 62 - tcp_aad.pml:77 - [((delayed_segments<2))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][62] = 1;
		if (!((((int)now.delayed_segments)<2)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 79: // STATE 63 - tcp_aad.pml:79 - [ato = 20] (0:0:1 - 1)
		IfNotBlocked
		reached[1][63] = 1;
		(trpt+1)->bup.oval = now.ato;
		now.ato = 20;
#ifdef VAR_RANGES
		logval("ato", now.ato);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 80: // STATE 65 - tcp_aad.pml:83 - [temp = (((iat_min*75)+(iat_curr*(100-75)))/100)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][65] = 1;
		(trpt+1)->bup.oval = ((P1 *)_this)->_5_3_1_temp;
		((P1 *)_this)->_5_3_1_temp = (((now.iat_min*75)+(((int)now.iat_curr)*(100-75)))/100);
#ifdef VAR_RANGES
		logval("Receiver:temp", ((P1 *)_this)->_5_3_1_temp);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 81: // STATE 66 - tcp_aad.pml:84 - [ato = ((temp*150)/100)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][66] = 1;
		(trpt+1)->bup.oval = now.ato;
		now.ato = ((((P1 *)_this)->_5_3_1_temp*150)/100);
#ifdef VAR_RANGES
		logval("ato", now.ato);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 82: // STATE 67 - tcp_aad.pml:88 - [((ato>20))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][67] = 1;
		if (!((now.ato>20)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 83: // STATE 68 - tcp_aad.pml:89 - [ato = 20] (0:0:1 - 1)
		IfNotBlocked
		reached[1][68] = 1;
		(trpt+1)->bup.oval = now.ato;
		now.ato = 20;
#ifdef VAR_RANGES
		logval("ato", now.ato);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 84: // STATE 73 - tcp_aad.pml:96 - [((ato<1))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][73] = 1;
		if (!((now.ato<1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 85: // STATE 74 - tcp_aad.pml:97 - [ato = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][74] = 1;
		(trpt+1)->bup.oval = now.ato;
		now.ato = 1;
#ifdef VAR_RANGES
		logval("ato", now.ato);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 86: // STATE 81 - tcp_aad.pml:104 - [assert(((ato>=1)&&(ato<=20)))] (0:0:0 - 5)
		IfNotBlocked
		reached[1][81] = 1;
		spin_assert(((now.ato>=1)&&(now.ato<=20)), "((ato>=1)&&(ato<=20))", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 87: // STATE 82 - tcp_aad.pml:106 - [printf('Receiver: Calculated ATO=%d (iat_min=%d, iat_curr=%d, delayed_segs=%d)\\n',ato,iat_min,iat_curr,delayed_segments)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][82] = 1;
		Printf("Receiver: Calculated ATO=%d (iat_min=%d, iat_curr=%d, delayed_segs=%d)\n", now.ato, now.iat_min, ((int)now.iat_curr), ((int)now.delayed_segments));
		_m = 3; goto P999; /* 0 */
	case 88: // STATE 84 - tcp_aad.pml:140 - [ack_timer_expiry = (current_time+ato)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][84] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_timer_expiry);
		now.ack_timer_expiry = (((int)now.current_time)+now.ato);
#ifdef VAR_RANGES
		logval("ack_timer_expiry", ((int)now.ack_timer_expiry));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 89: // STATE 85 - tcp_aad.pml:141 - [ack_scheduled = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][85] = 1;
		(trpt+1)->bup.oval = ((int)now.ack_scheduled);
		now.ack_scheduled = 1;
#ifdef VAR_RANGES
		logval("ack_scheduled", ((int)now.ack_scheduled));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 90: // STATE 86 - tcp_aad.pml:143 - [printf('Receiver: Scheduled ACK timer to expire at time=%d (ATO=%d)\\n',ack_timer_expiry,ato)] (0:0:0 - 1)
		IfNotBlocked
		reached[1][86] = 1;
		Printf("Receiver: Scheduled ACK timer to expire at time=%d (ATO=%d)\n", ((int)now.ack_timer_expiry), now.ato);
		_m = 3; goto P999; /* 0 */
	case 91: // STATE 92 - tcp_aad.pml:278 - [(((packets_received>=3)&&!(ack_scheduled)))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][92] = 1;
		if (!(((((int)now.packets_received)>=3)&& !(((int)now.ack_scheduled)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 92: // STATE 93 - tcp_aad.pml:280 - [printf('Receiver: All packets received and acknowledged\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[1][93] = 1;
		Printf("Receiver: All packets received and acknowledged\n");
		_m = 3; goto P999; /* 0 */
	case 93: // STATE 98 - tcp_aad.pml:283 - [-end-] (0:0:0 - 3)
		IfNotBlocked
		reached[1][98] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Sender */
	case 94: // STATE 1 - tcp_aad.pml:158 - [printf('Sender: Starting packet transmission\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		Printf("Sender: Starting packet transmission\n");
		_m = 3; goto P999; /* 0 */
	case 95: // STATE 2 - tcp_aad.pml:161 - [((packets_sent<3))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		if (!((((int)now.packets_sent)<3)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 96: // STATE 3 - tcp_aad.pml:163 - [pkt.seqno = next_seq_to_send] (0:0:1 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)_this)->pkt.seqno);
		((P0 *)_this)->pkt.seqno = ((int)now.next_seq_to_send);
#ifdef VAR_RANGES
		logval("Sender:pkt.seqno", ((int)((P0 *)_this)->pkt.seqno));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 97: // STATE 4 - tcp_aad.pml:164 - [pkt.timestamp = current_time] (0:0:1 - 1)
		IfNotBlocked
		reached[0][4] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)_this)->pkt.timestamp);
		((P0 *)_this)->pkt.timestamp = ((int)now.current_time);
#ifdef VAR_RANGES
		logval("Sender:pkt.timestamp", ((int)((P0 *)_this)->pkt.timestamp));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 98: // STATE 5 - tcp_aad.pml:167 - [network_chan!pkt.seqno,pkt.timestamp] (0:0:0 - 1)
		IfNotBlocked
		reached[0][5] = 1;
		if (q_full(now.network_chan))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[64];
			sprintf(simvals, "%d!", now.network_chan);
		sprintf(simtmp, "%d", ((int)((P0 *)_this)->pkt.seqno)); strcat(simvals, simtmp);		strcat(simvals, ",");
		sprintf(simtmp, "%d", ((int)((P0 *)_this)->pkt.timestamp)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.network_chan, 0, ((int)((P0 *)_this)->pkt.seqno), ((int)((P0 *)_this)->pkt.timestamp), 2);
		_m = 2; goto P999; /* 0 */
	case 99: // STATE 6 - tcp_aad.pml:169 - [printf('Sender: Sent packet seq=%d at time=%d\\n',pkt.seqno,current_time)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][6] = 1;
		Printf("Sender: Sent packet seq=%d at time=%d\n", ((int)((P0 *)_this)->pkt.seqno), ((int)now.current_time));
		_m = 3; goto P999; /* 0 */
	case 100: // STATE 7 - tcp_aad.pml:172 - [next_seq_to_send = (next_seq_to_send+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][7] = 1;
		(trpt+1)->bup.oval = ((int)now.next_seq_to_send);
		now.next_seq_to_send = (((int)now.next_seq_to_send)+1);
#ifdef VAR_RANGES
		logval("next_seq_to_send", ((int)now.next_seq_to_send));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 101: // STATE 8 - tcp_aad.pml:173 - [packets_sent = (packets_sent+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][8] = 1;
		(trpt+1)->bup.oval = ((int)now.packets_sent);
		now.packets_sent = (((int)now.packets_sent)+1);
#ifdef VAR_RANGES
		logval("packets_sent", ((int)now.packets_sent));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 102: // STATE 9 - tcp_aad.pml:175 - [((packets_sent>=3))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][9] = 1;
		if (!((((int)now.packets_sent)>=3)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 103: // STATE 10 - tcp_aad.pml:176 - [printf('Sender: All packets sent\\n')] (0:0:0 - 1)
		IfNotBlocked
		reached[0][10] = 1;
		Printf("Sender: All packets sent\n");
		_m = 3; goto P999; /* 0 */
	case 104: // STATE 15 - tcp_aad.pml:179 - [-end-] (0:0:0 - 3)
		IfNotBlocked
		reached[0][15] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

