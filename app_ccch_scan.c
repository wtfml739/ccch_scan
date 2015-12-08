#include <stdint.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>
#include <getopt.h>
#include <assert.h>
#include <arpa/inet.h>

#include <osmocom/core/msgb.h>
#include <osmocom/gsm/rsl.h>
#include <osmocom/gsm/tlv.h>
#include <osmocom/gsm/gsm48_ie.h>
#include <osmocom/gsm/gsm48.h>
#include <osmocom/core/signal.h>
#include <osmocom/gsm/protocol/gsm_04_08.h>
#include <osmocom/core/gsmtap_util.h>
#include <osmocom/core/bits.h>
#include <osmocom/gsm/a5.h>

#include <osmocom/bb/common/logging.h>
#include <osmocom/bb/misc/rslms.h>
#include <osmocom/bb/misc/layer3.h>
#include <osmocom/bb/common/osmocom_data.h>
#include <osmocom/bb/common/l1ctl.h>
#include <osmocom/bb/common/l23_app.h>

#include <l1ctl_proto.h>

#include <osmocom/bb/misc/xcch.h>

#include "cellid.c"
#include "assignment.c"

struct osmocom_ms *g_ms;

extern struct gsmtap_inst *gsmtap_inst;

enum dch_state_t {
	DCH_NONE,
	DCH_WAIT_EST,
	DCH_ACTIVE,
	DCH_WAIT_REL,
};

static struct {
	int			has_si1;
	int			has_si3;
	int			ccch_mode;

	enum dch_state_t	dch_state;
	uint8_t			dch_nr;
	int			dch_badcnt;
	int			dch_ciph;
	int			immasscnt;
	FILE *			fh;
	struct osmocom_ms	*ms;

	int			sniffing;
	int			sms;
	int			finding;
	int			tmsicnt;
	int			mincnt;
	sbit_t			bursts_dl[116 * 4];
	sbit_t			bursts_ul[116 * 4];

	struct gsm_sysinfo_freq	cell_arfcns[1024];

	uint8_t			kc[8];
	uint8_t			wanted_tmsi[4];
	uint8_t			matchcnt;
	uint8_t			tmsi_matched;
} app_state;

enum sms_mode {
	SMS_CP_DATA,
	SMS_CP_ACK,
	SMS_RP_ACK,
	SMS_NONE
};

struct _sms_state {
	uint8_t cp_user_length;
	uint8_t rp_data_length;
	uint8_t tp_ud_len;
	uint8_t parts;
	uint8_t cpart;
	int ptr;
	int skip;
	char smc[32];
	char from[32];
	char to[32];
	char buf[256];
	char text[1024];
	char utf[1024];
} sms_state;

struct _tmsis_ {
	uint8_t		tmsi[4];
	char 		cnt;
} tmsis[300];

/*! \brief Convert UCS2 string to UTF8 string.
 *  \param[out] decoded pointer to buffer which will contain decoded string
 *  \param[in] decoded_buf_length length of 'decoded' buffer
 *  \param[in] user_data pointer to buffer which contains UCS2 string
 *  \param[in] length length of 'user_data' buffer
 *  \returns length of decoded string
 *
 * This function will convert UCS2 string to UTF-8 string. 
 */
uint16_t osmo_ucs2_to_utf8_decode(char *decoded, const uint16_t decoded_buf_length, const uint8_t *user_data, const uint8_t length)
{
	uint16_t i, j = 0;

	for (i = 0; i < length; i++) {
		uint16_t ucs2;

		ucs2 = ((user_data[2 * i] << 8) | user_data[2 * i + 1]);
		if (ucs2 < 0x80) {
			if (j >= decoded_buf_length-1)
				break;
			decoded[j++] = ucs2;
		} else if (ucs2 >= 0x80  && ucs2 < 0x800) {
			if (j >= decoded_buf_length-2)
				break;
			decoded[j++] = (ucs2 >> 6)   | 0xC0;
			decoded[j++] = (ucs2 & 0x3F) | 0x80;
		} else if (ucs2 >= 0x800 && ucs2 < 0xFFFF) {
			if (j >= decoded_buf_length-3)
				break;
			decoded[j++] = ((ucs2 >> 12)       ) | 0xE0;
			decoded[j++] = ((ucs2 >> 6 ) & 0x3F) | 0x80;
			decoded[j++] = ((ucs2      ) & 0x3F) | 0x80;
		}
	}
	decoded[j] = '\0';
	//decoded[j+1] = '\0';

	return j;
}

static char *decode_bcd(uint8_t *data, uint8_t length)
{
	int i, j = 0;
	static char result[32], c;

	for (i = 0; i < (length << 1); i++) {
		if ((i & 1))
			c = (data[i >> 1] >> 4);
		else
			c = (data[i >> 1] & 0xf);
		if (c == 0xf)
			break;
		result[j++] = c + '0';
		if (j == sizeof(result) - 1)
			break;
	}
	result[j] = '\0';

	return result;
}

static char * osmo_int16_dump(const unsigned char *buf, int len, char *delim)
{
	int i;
	char hexd_buff[1024];
	char *cur = hexd_buff;

	hexd_buff[0] = 0;
	for (i = 0; i < len; i++) {
		int len_remain = sizeof(hexd_buff) - (cur - hexd_buff);
		if (len_remain <= 0)
			break;
		int rc = snprintf(cur, len_remain, "%d%s", buf[i*2]+buf[i*2+1]*256, delim);
		if (rc <= 0)
			break;
		cur += rc;
	}
	hexd_buff[sizeof(hexd_buff)-1] = 0;
	return hexd_buff;
}

inline int not_zero(uint8_t *t, unsigned size)
{
        unsigned i;

        for (i=0; i<size; i++) {
                if (t[i])
                        break;
        }

        if (i == size)
                return 0;
        else
                return 1;
}

static void dump_bcch(struct osmocom_ms *ms, uint8_t tc, const uint8_t *data)
{
	struct gsm48_system_information_type_header *si_hdr;
	si_hdr = (struct gsm48_system_information_type_header *) data;
	struct gsm48_system_information_type_3 *si3 =
		(struct gsm48_system_information_type_3 *) data;

	/* GSM 05.02 §6.3.1.3 Mapping of BCCH data */
	switch (si_hdr->system_information) {
	case GSM48_MT_RR_SYSINFO_1:
		if (!app_state.has_si1) {
			struct gsm48_system_information_type_1 *si1 =
				(struct gsm48_system_information_type_1 *)data;

			gsm48_decode_freq_list(app_state.cell_arfcns,
			                       si1->cell_channel_description,
					       sizeof(si1->cell_channel_description),
					       0xff, 0x01);

			app_state.has_si1 = 1;
			LOGP(DRR, LOGL_ERROR, "SI1 received.\n");
		}
		break;
	case GSM48_MT_RR_SYSINFO_2:
		break;
	case GSM48_MT_RR_SYSINFO_3:
		if (app_state.ccch_mode == CCCH_MODE_NONE) {
			struct gsm48_system_information_type_3 *si3 =
				(struct gsm48_system_information_type_3 *)data;

			if (si3->control_channel_desc.ccch_conf == RSL_BCCH_CCCH_CONF_1_C)
				app_state.ccch_mode = CCCH_MODE_COMBINED;
			else
				app_state.ccch_mode = CCCH_MODE_NON_COMBINED;
			////ccch_conf?
			printf("arfcn=%d\tccch_conf = %d \n", ms->test_arfcn, si3->control_channel_desc.ccch_conf);

			l1ctl_tx_ccch_mode_req(ms, app_state.ccch_mode);
		}

		if (!app_state.has_si3) {
			set_cid(si3->lai.digits, si3->lai.lac, si3->cell_identity);
			LOGP(DRR, LOGL_ERROR, "SI3 received.\n");
			app_state.has_si3 = 1;
		}
		break;
	case GSM48_MT_RR_SYSINFO_4:
		break;
	case GSM48_MT_RR_SYSINFO_5:
		break;
	case GSM48_MT_RR_SYSINFO_6:
		break;
	case GSM48_MT_RR_SYSINFO_7:
		break;
	case GSM48_MT_RR_SYSINFO_8:
		break;
	case GSM48_MT_RR_SYSINFO_9:
		break;
	case GSM48_MT_RR_SYSINFO_13:
		break;
	case GSM48_MT_RR_SYSINFO_16:
		break;
	case GSM48_MT_RR_SYSINFO_17:
		break;
	case GSM48_MT_RR_SYSINFO_2bis:
		break;
	case GSM48_MT_RR_SYSINFO_2ter:
		break;
	case GSM48_MT_RR_SYSINFO_2quater:
		break;
	case GSM48_MT_RR_SYSINFO_5bis:
		break;
	case GSM48_MT_RR_SYSINFO_5ter:
		break;
	default:
		LOGP(DRR, LOGL_ERROR, "Unknown SI: %d\n",
		     si_hdr->system_information);
		break;
	};
}

void parse_chandesc(struct gsm48_chan_desc *chan_desc,
			uint8_t mob_alloc_len,
			const uint8_t *mob_alloc,
			struct gsm_assignment *ga)
{
	ga->chan_nr = chan_desc->chan_nr;
	ga->h = chan_desc->h0.h;

	if (!ga->h) {
		/* Non-hopping */
		ga->tsc = chan_desc->h0.tsc;
		ga->h0.band_arfcn = chan_desc->h0.arfcn_low | (chan_desc->h0.arfcn_high << 8);
	} else {
		/* Hopping */
		uint16_t arfcn;
		int i, j, k;

		ga->tsc = chan_desc->h1.tsc;
		ga->h1.hsn = chan_desc->h1.hsn;
		ga->h1.maio = chan_desc->h1.maio_low | (chan_desc->h1.maio_high << 2);

		/* decode mobile allocation */
		ga->h1.ma_len = 0;
		for (i=1, j=0; i<=1024; i++) {
			arfcn = i & 1023;
			if (app_state.cell_arfcns[arfcn].mask & 0x01) {
				k = mob_alloc_len - (j>>3) - 1;
				if (mob_alloc[k] & (1 << (j&7))) {
					ga->h1.ma[ga->h1.ma_len++] = arfcn;
				}
				j++;
			}
		}
	}
}

void follow_assignment(struct osmocom_ms *ms, struct gsm_assignment *ga)
{
	/* Set state */
	app_state.dch_state = DCH_WAIT_EST;
	app_state.dch_nr = ga->chan_nr;
	app_state.dch_badcnt = 0;
	
	app_state.immasscnt += 1;

	/* Tune to new channel */
	if (!ga->h) {
		l1ctl_tx_dm_est_req_h0(ms,
			ga->h0.band_arfcn, ga->chan_nr, ga->tsc,
			GSM48_CMODE_SIGN, 0);
		printf("Follow Imm Ass #%d\tat ARFCN:%d\tTimeslot:%d\tTSC:%d\n", app_state.immasscnt, ga->h0.band_arfcn, ga->chan_nr & 0x7, ga->tsc);

	} else {
		l1ctl_tx_dm_est_req_h1(ms,
			ga->h1.maio, ga->h1.hsn, ga->h1.ma, ga->h1.ma_len,
			ga->chan_nr, ga->tsc,
			GSM48_CMODE_SIGN, 0);
		printf("Follow Imm Ass #%d\tat Hopping MAIO:%d\tHSN:%d\tMA:%s\tTimeslot:%d\tTSC:%d\n", app_state.immasscnt, ga->h1.maio, ga->h1.hsn,
			osmo_int16_dump(ga->h1.ma, ga->h1.ma_len, " "), ga->chan_nr & 0x7, ga->tsc);
	}
}

void gsm48_rx_imm_ass(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_imm_ass *ia = msgb_l3(msg);
	struct gsm_assignment ga;

	if (app_state.finding==1)
		return;

	/* only our tmsi */
	if (!app_state.tmsi_matched && not_zero(app_state.wanted_tmsi, 4))
		return;

	/* Discard packet TBF assignement */
	if (ia->page_mode & 0xf0)
		return;

	/* If we're not ready yet, or just busy ... */
	if ((!(app_state.has_si1 && app_state.has_si3)) || (app_state.dch_state != DCH_NONE))
		return;

	parse_chandesc(&ia->chan_desc, ia->mob_alloc_len, ia->mob_alloc, &ga);

	follow_assignment(ms, &ga);
}

void gsm48_rx_imm_ass_ext(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_imm_ass_ext *iae = msgb_l3(msg);
	struct gsm_assignment ga;

	printf("EXT!!!\n");
	fflush(stdout);

	/* First */
	parse_chandesc(&iae->chan_desc1, iae->mob_alloc_len, iae->mob_alloc, &ga);

	/* Second */
	parse_chandesc(&iae->chan_desc2, iae->mob_alloc_len, iae->mob_alloc, &ga);
}

static const char *pag_print_mode(int mode)
{
	switch (mode) {
	case 0:
		return "Normal paging";
	case 1:
		return "Ext.ed paging";
	case 2:
		return "Paging reorganization";
	case 3:
		return "Same as before";
	default:
		return "invalid";
	}
}

static char *chan_need(int need)
{
	switch (need) {
	case 0:
		return "any  ";
	case 1:
		return "sdch ";
	case 2:
		return "tch/f";
	case 3:
		return "tch/h";
	default:
		return "invalid";
	}
}

static char *mi_type_to_string(int type)
{
	switch (type) {
	case GSM_MI_TYPE_NONE:
		return "none";
	case GSM_MI_TYPE_IMSI:
		return "IMSI";
	case GSM_MI_TYPE_IMEI:
		return "IMEI";
	case GSM_MI_TYPE_IMEISV:
		return "IMEISV";
	case GSM_MI_TYPE_TMSI:
		return "TMSI";
	default:
		return "invalid";
	}
}

void tmsi_match(uint8_t *t)
{
	if(app_state.finding==1){
		int i;
		int f=0;
		for(i=0; i < app_state.tmsicnt; i++){
			if(!memcmp(t, tmsis[i].tmsi, 4)) {
				tmsis[i].cnt += 1;
				f=1;
				//printf("TMSI:#%d, %s, %d \tTotal: %d\n", i, osmo_hexdump(t,4), tmsis[i].cnt, app_state.tmsicnt);
				if(tmsis[i].cnt > app_state.mincnt){
					printf("Possible TMSI: #%d, \t%s, %d times\n", i, osmo_hexdump(t,4), tmsis[i].cnt);
				}
			}
		}
		if((f==0)&&(app_state.tmsicnt<300)){			
			app_state.tmsicnt += 1;
			memcpy(tmsis[i].tmsi,t,4);
			tmsis[i].cnt = 1;
			printf("New TMSI:#%d, %s \tTotal: %d\n", i, osmo_hexdump(t,4), app_state.tmsicnt);
		}

		return;
	}
	
	if(!memcmp(t, app_state.wanted_tmsi, 4)) {
		app_state.tmsi_matched = 1;
		///tmsi match
		printf("TMSI Match %s\n", osmo_hexdump(t,4));
	}
}

/**
 * This can contain two MIs. The size checking is a bit of a mess.
 */
static int gsm48_rx_paging_p1(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_paging1 *pag;
	int len1, len2, mi_type, tag;
	char mi_string[GSM48_MI_SIZE];

	/* is there enough room for the header + LV? */
	if (msgb_l3len(msg) < sizeof(*pag) + 2) {
		LOGP(DRR, LOGL_ERROR, "PagingRequest is too short.\n");
		return -1;
	}

	pag = msgb_l3(msg);
	len1 = pag->data[0];
	mi_type = pag->data[1] & GSM_MI_TYPE_MASK;

	if (msgb_l3len(msg) < sizeof(*pag) + 2 + len1) {
		LOGP(DRR, LOGL_ERROR, "PagingRequest with wrong MI\n");
		return -1;
	}

	if (mi_type != GSM_MI_TYPE_NONE) {
		gsm48_mi_to_string(mi_string, sizeof(mi_string), &pag->data[1], len1);
		/*LOGP(DRR, LOGL_NOTICE, "Paging1: %s chan %s to %s M(%s) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed1),
		     mi_type_to_string(mi_type),
		     mi_string);
		*/
		tmsi_match(&pag->data[2]);
	}

	/* check if we have a MI type in here */
	if (msgb_l3len(msg) < sizeof(*pag) + 2 + len1 + 3)
		return 0;

	tag = pag->data[2 + len1 + 0];
	len2 = pag->data[2 + len1 + 1];
	mi_type = pag->data[2 + len1 + 2] & GSM_MI_TYPE_MASK;
	if (tag == GSM48_IE_MOBILE_ID && mi_type != GSM_MI_TYPE_NONE) {
		if (msgb_l3len(msg) < sizeof(*pag) + 2 + len1 + 3 + len2) {
			LOGP(DRR, LOGL_ERROR, "Optional MI does not fit here.\n");
			return -1;
		}

		gsm48_mi_to_string(mi_string, sizeof(mi_string), &pag->data[2 + len1 + 2], len2);
		/*LOGP(DRR, LOGL_NOTICE, "Paging1: %s chan %s to %s M(%s) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed2),
		     mi_type_to_string(mi_type),
		     mi_string);
		*/
		tmsi_match(&pag->data[2 + len1 + 3]);
	}
	return 0;
}

static int gsm48_rx_paging_p2(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_paging2 *pag;
	int tag, len, mi_type;
	char mi_string[GSM48_MI_SIZE];

	if (msgb_l3len(msg) < sizeof(*pag)) {
		LOGP(DRR, LOGL_ERROR, "Paging2 message is too small.\n");
		return -1;
	}

	pag = msgb_l3(msg);
	/*LOGP(DRR, LOGL_NOTICE, "Paging2: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed1), ntohl(pag->tmsi1));
	*/
	tmsi_match((uint8_t *)&pag->tmsi1);

	/*LOGP(DRR, LOGL_NOTICE, "Paging2: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed1), ntohl(pag->tmsi2));
	*/
	tmsi_match((uint8_t *)&pag->tmsi2);

	/* no optional element */
	if (msgb_l3len(msg) < sizeof(*pag) + 3)
		return 0;

	tag = pag->data[0];
	len = pag->data[1];
	mi_type = pag->data[2] & GSM_MI_TYPE_MASK;

	if (tag != GSM48_IE_MOBILE_ID)
		return 0;

	if (msgb_l3len(msg) < sizeof(*pag) + 3 + len) {
		LOGP(DRR, LOGL_ERROR, "Optional MI does not fit in here\n");
		return -1;
	}

	gsm48_mi_to_string(mi_string, sizeof(mi_string), &pag->data[2], len);
	/*LOGP(DRR, LOGL_NOTICE, "Paging2: %s chan %s to %s M(%s) \n",
	     pag_print_mode(pag->pag_mode),
	     "n/a  ",
	     mi_type_to_string(mi_type),
	     mi_string);
	*/
	tmsi_match(&pag->data[3]);

	return 0;
}

static int gsm48_rx_paging_p3(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_paging3 *pag;

	if (msgb_l3len(msg) < sizeof(*pag)) {
		LOGP(DRR, LOGL_ERROR, "Paging3 message is too small.\n");
		return -1;
	}

	pag = msgb_l3(msg);
	/*LOGP(DRR, LOGL_NOTICE, "Paging3: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed1), ntohl(pag->tmsi1));
	*/
	tmsi_match((uint8_t *)&pag->tmsi1);

	/*LOGP(DRR, LOGL_NOTICE, "Paging3: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed1), ntohl(pag->tmsi2));
	*/
	tmsi_match((uint8_t *)&pag->tmsi2);

	/*LOGP(DRR, LOGL_NOTICE, "Paging3: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed3), ntohl(pag->tmsi3));
	*/
	tmsi_match((uint8_t *)&pag->tmsi3);

	/*LOGP(DRR, LOGL_NOTICE, "Paging3: %s chan %s to TMSI M(%u) \n",
		     pag_print_mode(pag->pag_mode),
		     chan_need(pag->cneed4), ntohl(pag->tmsi4));
	*/
	tmsi_match((uint8_t *)&pag->tmsi4);

	return 0;
}

static char *
gen_filename(struct osmocom_ms *ms, struct l1ctl_burst_ind *bi)
{
	static char buffer[256];
	time_t d;
	struct tm lt;

	time(&d);
	localtime_r(&d, &lt);

	snprintf(buffer, 256, "%s_%04d%02d%02d_%02d%02d_%d_%d_%02x.dat",
		get_cid_str(),
		lt.tm_year + 1900, lt.tm_mon, lt.tm_mday,
		lt.tm_hour, lt.tm_min,
		ms->test_arfcn,
		ntohl(bi->frame_nr),
		bi->chan_nr
	);

	return buffer;
}

void layer3_rx_burst(struct osmocom_ms *ms, struct msgb *msg)
{
	struct l1ctl_burst_ind *bi;
	uint16_t arfcn;
	int ul, do_rel=0;

	/* Header handling */
	bi = (struct l1ctl_burst_ind *) msg->l1h;

	arfcn = ntohs(bi->band_arfcn);
	ul = !!(arfcn & ARFCN_UPLINK);

	/* Check for channel start */
	if (app_state.dch_state == DCH_WAIT_EST) {
		if (bi->chan_nr == app_state.dch_nr) {
			if (bi->snr > 64) {
				/* Change state */
				app_state.dch_state = DCH_ACTIVE;
				app_state.dch_badcnt = 0;
				app_state.tmsi_matched = 0;

				/* Open output */
				app_state.fh = fopen(gen_filename(ms, bi), "wb");
			} else {
				/* Abandon ? */
				do_rel = (app_state.dch_badcnt++) >= 4;
			}
		}
	}

	/* Check for channel end */
	if (app_state.dch_state == DCH_ACTIVE) {
		if (!ul) {
			/* Bad burst counting */
			if (bi->snr < 64)
				app_state.dch_badcnt++;
			else if (app_state.dch_badcnt >= 2)
				app_state.dch_badcnt -= 2;
			else
				app_state.dch_badcnt = 0;

			/* Release condition */
			if (app_state.dch_nr < 0x20)
				do_rel = app_state.dch_badcnt >= 100;
			else
				do_rel = app_state.dch_badcnt >= 6;
		}
	}

	/* Save the burst and try decoding */
	if (app_state.dch_state == DCH_ACTIVE) {
		local_burst_decode(bi);
		fwrite(bi, sizeof(*bi), 1, app_state.fh);
	}

	/* Release ? */
	if (do_rel) {
		/* L1 release */
		l1ctl_tx_dm_rel_req(ms);

		/* tune back to BCCH */
		l1ctl_tx_fbsb_req(ms, ms->test_arfcn,
				L1CTL_FBSB_F_FB01SB, 100, 0,
				app_state.ccch_mode);
		printf("Back to BCCH\n");

		/* Change state */
		app_state.dch_state = DCH_WAIT_REL;
		app_state.dch_badcnt = 0;
		app_state.dch_ciph = 0;

		/* Close output */
		if (app_state.fh) {
			fclose(app_state.fh);
			app_state.fh = NULL;
		}

		/* proceed only on correct TMSI */
		if (not_zero(app_state.wanted_tmsi, 4) && !app_state.tmsi_matched)
			return;

		/* reset TMSI match */
		app_state.tmsi_matched = 0;

		/* releasing everything */
		app_state.sniffing = 0;
		app_state.sms = 0;
		
		//TODO deal with multi-part SMS
		//if((sms_state.parts > 1) && (sms_state.cpart < sms_state.parts)){
		memset(&sms_state, 0, sizeof(sms_state));
		sms_state.cpart = 1;
		sms_state.parts = 1;
		
	}
}

int gsm48_rx_ccch(struct msgb *msg, struct osmocom_ms *ms)
{
	struct gsm48_system_information_type_header *sih = msgb_l3(msg);
	int rc = 0;

	/* CCCH marks the end of WAIT_REL */
	if (app_state.dch_state == DCH_WAIT_REL)
		app_state.dch_state = DCH_NONE;

	if (sih->rr_protocol_discriminator != GSM48_PDISC_RR) {
		return 0;
	}

	switch (sih->system_information) {
	case GSM48_MT_RR_PAG_REQ_1:
		gsm48_rx_paging_p1(msg, ms);
		break;
	case GSM48_MT_RR_PAG_REQ_2:
		gsm48_rx_paging_p2(msg, ms);
		break;
	case GSM48_MT_RR_PAG_REQ_3:
		gsm48_rx_paging_p3(msg, ms);
		break;
	case GSM48_MT_RR_IMM_ASS:
		gsm48_rx_imm_ass(msg, ms);
		break;
	case  GSM48_MT_RR_IMM_ASS_EXT:
		gsm48_rx_imm_ass_ext(msg, ms);
		break;
	case GSM48_MT_RR_NOTIF_NCH:
		/* notification for voice call groups and such */
		break;
	case 0x07:
		/* wireshark know that this is SI2 quater and for 3G interop */
		break;
	default:
		LOGP(DRR, LOGL_NOTICE, "unknown PCH/AGCH type 0x%02x\n",
			sih->system_information);
		rc = -EINVAL;
	}

	return rc;
}

int gsm48_rx_bcch(struct msgb *msg, struct osmocom_ms *ms)
{
	/* BCCH marks the end of WAIT_REL */
	if (app_state.dch_state == DCH_WAIT_REL)
		app_state.dch_state = DCH_NONE;

	/* FIXME: we have lost the gsm frame time until here, need to store it
	 * in some msgb context */
	//dump_bcch(dl->time.tc, ccch->data);
	dump_bcch(ms, 0, msg->l3h);

	return 0;
}

void local_burst_decode(struct l1ctl_burst_ind *bi)
{
	uint16_t arfcn;
	uint32_t fn;
	uint8_t cbits, tn, lch_idx;
	int ul, bid, i;
	sbit_t *bursts;
	ubit_t bt[116];
	uint8_t *ptr = 0;
	uint8_t len = 0;
	uint8_t SMClen = 0;
	uint8_t Destlen = 0;
	uint8_t Fromlen = 0;
	uint8_t Fromlen0 = 0;
	uint8_t UDHlen = 0;
	uint8_t Hdrlen = 0;
	uint8_t DCS = 0;
	
	/* Get params (Only for SDCCH and SACCH/{4,8,F,H}) */
	arfcn  = ntohs(bi->band_arfcn);

	fn     = ntohl(bi->frame_nr);
	ul     = !!(arfcn & ARFCN_UPLINK);
	bursts = ul ? app_state.bursts_ul : app_state.bursts_dl;

	cbits  = bi->chan_nr >> 3;
	tn     = bi->chan_nr & 7;

	bid    = -1;

	if (cbits == 0x01) {			/* TCH/F */
		lch_idx = 0;
		if (bi->flags & BI_FLG_SACCH) {
			uint32_t fn_report;
			fn_report = (fn - (tn * 13) + 104) % 104;
			bid = (fn_report - 12) / 26;
		}
	} else if ((cbits & 0x1e) == 0x02) {	/* TCH/H */
		lch_idx = cbits & 1;
		if (bi->flags & BI_FLG_SACCH) {
			uint32_t fn_report;
			uint8_t tn_report = (tn & ~1) | lch_idx;
			fn_report = (fn - (tn_report * 13) + 104) % 104;
			bid = (fn_report - 12) / 26;
		}
	} else if ((cbits & 0x1c) == 0x04) {	/* SDCCH/4 */
		lch_idx = cbits & 3;
		bid = bi->flags & 3;
	} else if ((cbits & 0x18) == 0x08) {	/* SDCCH/8 */
		lch_idx = cbits & 7;
		bid = bi->flags & 3;
	}

	if (bid == -1)
		return;

	/* Clear if new set */
	if (bid == 0)
		memset(bursts, 0x00, 116 * 4);

	/* Unpack (ignore hu/hl) */
	osmo_pbit2ubit_ext(bt,  0, bi->bits,  0, 57, 0);
	osmo_pbit2ubit_ext(bt, 59, bi->bits, 57, 57, 0);
	bt[57] = bt[58] = 1;

	/* A5/x */
	if (app_state.dch_ciph) {
		ubit_t ks_dl[114], ks_ul[114], *ks = ul ? ks_ul : ks_dl;
		osmo_a5(app_state.dch_ciph, app_state.kc, fn, ks_dl, ks_ul);
		for (i= 0; i< 57; i++)  bt[i] ^= ks[i];
		for (i=59; i<116; i++)  bt[i] ^= ks[i-2];
	}

	/* Convert to softbits */
	for (i=0; i<116; i++)
		bursts[(116*bid)+i] = bt[i] ? - (bi->snr >> 1) : (bi->snr >> 1);

	/* If last, decode */
	if (bid == 3)
	{
		uint8_t l2[23];
		int rv;
		rv = xcch_decode(l2, bursts);

		if (rv == 0)
		{
			uint8_t chan_type, chan_ts, chan_ss;
			uint8_t gsmtap_chan_type;

			/* Send to GSMTAP */
			rsl_dec_chan_nr(bi->chan_nr, &chan_type, &chan_ss, &chan_ts);
			gsmtap_chan_type = chantype_rsl2gsmtap(
				chan_type,
				bi->flags & BI_FLG_SACCH ? 0x40 : 0x00
			);
			gsmtap_send(gsmtap_inst,
				arfcn, chan_ts, gsmtap_chan_type, chan_ss,
				ntohl(bi->frame_nr), bi->rx_level, bi->snr,
				l2, sizeof(l2)
			);
			if(app_state.sms == 1){
				if((l2[0]==0x0f) && ((l2[1] & 0x01)==0)){
					//printf("SMS PAYLOAD: %s\n", osmo_hexdump(l2, sizeof(l2)));
				
					memcpy(sms_state.buf + sms_state.ptr, l2+3, l2[2] >> 2);
					sms_state.ptr += l2[2] >> 2;
					//printf("sms ptr %d, text %s\n", sms_state.ptr, osmo_hexdump(sms_state.buf, sms_state.ptr));
					if((l2[2] & 0x03)==1){//sms ending
						printf("Ending\n");
						app_state.sms = 0;
						SMClen = sms_state.buf[5];
						strcpy(sms_state.smc, decode_bcd(sms_state.buf+5+2, SMClen));
						Fromlen0 = sms_state.buf[5+1+SMClen+1+1+1];
						//assert(Fromlen0 >= 32);
						Fromlen = (Fromlen0+1)/2 + 1;				
						printf("Fromlen0=%d\tFromlen=%d\n",Fromlen0,Fromlen);
						strncpy(sms_state.from, decode_bcd(sms_state.buf+5+1+SMClen+2+1+1+1, Fromlen), Fromlen0);
						DCS = sms_state.buf[5+1+SMClen+2+1+1+Fromlen+1];
						Hdrlen = 5+1+SMClen+2+1+1+Fromlen+10;
						sms_state.tp_ud_len = sms_state.buf[Hdrlen-1];
						if((sms_state.buf[5+1+SMClen+1+1] & 0x40) == 0x40){//has user data header
							UDHlen = sms_state.buf[5+1+SMClen+2+1+1+Fromlen+10];
							sms_state.parts = sms_state.buf[5+1+SMClen+2+1+1+Fromlen+10+UDHlen-1];
							sms_state.cpart = sms_state.buf[5+1+SMClen+2+1+1+Fromlen+10+UDHlen];
							Hdrlen += UDHlen + 1;
							switch(DCS){
								case 8:
									sms_state.tp_ud_len = osmo_ucs2_to_utf8_decode(sms_state.utf, 1024, sms_state.buf+Hdrlen, sms_state.ptr-Hdrlen);
									break;
								case 4:
									memcpy(sms_state.utf,"MMS Message.",sizeof("MMS Message."));
									break;
								default:
									gsm_7bit_decode(sms_state.utf, sms_state.buf+Hdrlen, sms_state.tp_ud_len); //7Bit
							}
							printf("Multi-part sms part: %d of %d\nptr: %d, text: %s\n", sms_state.cpart, sms_state.parts, sms_state.ptr, osmo_hexdump(sms_state.buf, sms_state.ptr));
							printf("SMS From: %s\tSMC: %s\n",sms_state.from, sms_state.smc);
							printf("Decode:\n%s\n", sms_state.utf);
							if(sms_state.cpart>1){//appending
								memcpy(sms_state.text + sms_state.skip , sms_state.buf+Hdrlen, sms_state.ptr-Hdrlen);
								sms_state.skip += sms_state.ptr-Hdrlen;
							}
							else{//first part
								memcpy(sms_state.text, sms_state.buf, sms_state.ptr);
								sms_state.skip += sms_state.ptr;
							}
							//printf("sms skip: %d\ntext:%s\n", sms_state.skip, osmo_hexdump(sms_state.text, sms_state.skip));
							//printf("whole sms len: %d, SMClen: %d, Fromlen: %d, UDHlen: %d \n", sms_state.skip, SMClen, Fromlen, UDHlen);
						
						}
						else{
							switch(DCS){
								case 8:
									sms_state.tp_ud_len = osmo_ucs2_to_utf8_decode(sms_state.utf, 1024, sms_state.buf+Hdrlen, sms_state.ptr-Hdrlen);
									break;
								case 4:
									memcpy(sms_state.utf,"MMS Message.",sizeof("MMS Message."));
									break;
								default:
									gsm_7bit_decode(sms_state.utf, sms_state.buf+Hdrlen, sms_state.tp_ud_len); //7Bit
							}
							printf("Single sms ptr: %d, text: %s\n", sms_state.ptr, osmo_hexdump(sms_state.buf, sms_state.ptr));
							printf("SMS From: %s\tSMC: %s\n",sms_state.from, sms_state.smc);
							printf("Decode:\n%s\n", sms_state.utf);
							//memcpy(sms_state.text, sms_state.buf, sms_state.ptr);
							sms_state.parts = 1;
							sms_state.skip = 0;
						}
										
					}
				}
			}
			else{
				if((l2[0]==0x0f) && ((l2[1] & 0x01)==0) && (l2[3]==0x09) && (l2[4]==0x01)){
					app_state.sms = 1;
					sms_state.ptr = 0;
					sms_state.skip = 0; //TODO: handle with Multi-part SMS

					printf("Starting\nSMS PAYLOAD: %s\n", osmo_hexdump(l2, sizeof(l2)));
					sms_state.cp_user_length = l2[5]+3; /* read cp-data length and skip length byte */
					//printf("sms cp user length %d\n", sms_state.cp_user_length); 
					
					memcpy(sms_state.buf, l2+3, l2[2] >> 2);
					sms_state.ptr += l2[2] >> 2;
					//printf("sms ptr %d, text %s\n", sms_state.ptr, osmo_hexdump(sms_state.buf, l2[2] >> 2));
				}
				
			}
			/* Crude CIPH.MOD.COMMAND detect */
			if ((l2[3] == 0x06) && (l2[4] == 0x35) && (l2[5] & 1))
				app_state.dch_ciph = 1 + ((l2[5] >> 1) & 7);
		}
	}
}

void layer3_app_reset(void)
{
	/* Reset state */
	app_state.has_si1 = 0;
	app_state.has_si3 = 0;
	app_state.ccch_mode = CCCH_MODE_NONE;
	app_state.dch_state = DCH_NONE;
	app_state.dch_badcnt = 0;
	app_state.dch_ciph = 0;
	app_state.sniffing = 0;
	app_state.sms = 0;
	app_state.tmsi_matched = 0;
	
	memset(&sms_state, 0, sizeof(sms_state));

	if (app_state.fh)
		fclose(app_state.fh);
	app_state.fh = NULL;

	memset(&app_state.cell_arfcns, 0x00, sizeof(app_state.cell_arfcns));

	reset_cid();
}

static int signal_cb(unsigned int subsys, unsigned int signal,
		     void *handler_data, void *signal_data)
{
	struct osmocom_ms *ms;
	struct osmobb_msg_ind *mi;
	static unsigned loss_count = 0;

	if (subsys != SS_L1CTL)
		return 0;

	switch (signal) {
	case S_L1CTL_BURST_IND:
		mi = signal_data;
		loss_count = 0;
		layer3_rx_burst(mi->ms, mi->msg);
		break;

	case S_L1CTL_RESET:
		loss_count = 0;
		ms = signal_data;
		layer3_app_reset();
		return l1ctl_tx_fbsb_req(ms, ms->test_arfcn,
		                         L1CTL_FBSB_F_FB01SB, 100, 0,
		                         CCCH_MODE_NONE);
		break;

	case S_L1CTL_FBSB_RESP:
		loss_count = 0;
		break;

	case S_L1CTL_FBSB_ERR:
		ms = g_ms;
		return l1ctl_tx_fbsb_req(ms, ms->test_arfcn,
			L1CTL_FBSB_F_FB01SB, 100, 0, CCCH_MODE_COMBINED);
		break;
	
	case S_L1CTL_LOSS_IND:
		loss_count++;
		if (loss_count > 10) {
			loss_count = 0;
			return l1ctl_tx_fbsb_req(app_state.ms, app_state.ms->test_arfcn,
		                         L1CTL_FBSB_F_FB01SB, 100, 0,
		                         CCCH_MODE_NONE);
		}
		break;
	}
	return 0;
}


int l23_app_init(struct osmocom_ms *ms)
{
	int i;
	osmo_signal_register_handler(SS_L1CTL, &signal_cb, NULL);
	l1ctl_tx_reset_req(ms, L1CTL_RES_T_FULL);
	app_state.ms = ms;
	app_state.tmsicnt = 0;
	app_state.immasscnt = 0;
        g_ms = ms;
	for(i=0;i<300;i++){
		memset(&tmsis[i], 0, sizeof(tmsis[i]));
	}
	return layer3_init(ms);
}

static int l23_cfg_supported()
{
	return L23_OPT_TAP | L23_OPT_DBG;
}

static int l23_getopt_options(struct option **options)
{
	static struct option opts [] = {
		{"tmsi", 1, 0, 't'},
	};

	*options = opts;
	return ARRAY_SIZE(opts);
}

static int l23_cfg_print_help()
{
	printf("\nApplication specific\n");
	printf("  -k --kc KEY           Key to use to try to decipher DCCHs\n");
	printf("  -t --tmsi TMSI        Filter assignments with specified TMSI (paging only)\n");
	printf("  -f --count		Filter paging TMSI\n");

	return 0;
}

static int l23_cfg_handle(int c, const char *optarg)
{
	switch (c) {
	case 'k':
		if (osmo_hexparse(optarg, app_state.kc, 8) != 8) {
			fprintf(stderr, "Invalid Kc\n");
			exit(-1);
		}
		break;
	case 't':
		if (osmo_hexparse(optarg, app_state.wanted_tmsi, 4) != 4) {
			fprintf(stderr, "Invalid TMSI\n");
			exit(-1);
		}
		app_state.finding = 0;
		break;
	case 'f':
		app_state.finding = 1;
		app_state.mincnt= atoi(optarg);
		break;
	default:
		return -1;
	}
	return 0;
}

static struct l23_app_info info = {
	.copyright	= "Copyright (C) 2015 \n",
	.contribution	= "Contributions by Holger Hans Peter Freyther\n",
	.getopt_string	= "k:t:f:",
	.cfg_supported	= l23_cfg_supported,
	.cfg_getopt_opt = l23_getopt_options,
	.cfg_handle_opt	= l23_cfg_handle,
	.cfg_print_help	= l23_cfg_print_help,
};

struct l23_app_info *l23_app_info()
{
	return &info;
}
