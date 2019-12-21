# ovs_show_commands
Implementation of OVS show commands for GDB

Implemented commands:

vrf_show - Implementation of vrf/show command 

evpn_show - Implementation of evpn/show command (Need Mac address and check evpn_arp_vips)

vrf_list - Implementation of vrf/list command (Complete)

evpn_list - Implementation of evpn/list command (Complete)

ofproto_list - Implementation of ofproto/list (Complete)

dhcp_pool_show - Implementation of evpn/dhcp-pool-show (Need dhcp_static_entry_lookup_ip if statement completed)

dhcp_static_show - Implementation of evpn/dhcp-static-show (Complete)

dhcp_table - Implementation of evpn/dhcp-table (Need Mac address and VM IP)

dhcp_release_pool_show - Implementation of evpn/dhcp-release-pool-show (Complete)

spat_cfg_show - Implementation of vrf/spat-cfg-show (Complete)

spat_pending_cfg_show - Implementation of vrf/spat-pending-cfg-show (Complete)

sticky_ecmp_timeout - Implementation of ofproto/sticky-ecmp-timeout (Complete)

ubr_show - Implementation of ubr/show (Complete)

ipsec_list_cert - Implementation of ipsec/list-cert (Complete)

count_xfrm_state - Implementation of ipsec/count-xfrm-state (Check if FOR_EACH is satisfied)

dpdk_push_cfg - Implementation of ipsec/dpdk-push-cfg (Complete)

hub_group_config - Implementation of ofproto/hub-group-config (Need to check if if/else statements satisfied)

gw_group_config - Implementation of ofproto/gw-group-config (Need to check if if/else statements satisfied)

lport_show - Implementation of lport/show (Need FOR_EACH loops completed)