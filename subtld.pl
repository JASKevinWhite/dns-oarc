#!/usr/local/bin/perl

use strict;

###############################################################################
# 
# subtld.pl
#
# Kevin White
# kwhite@jasadvisors.com
# JAS Global Advisors
#
# Incorporating original shell and Perl extraction/processing/filtering
# code from:
# Roy Hooper <roy@demandmedia.com>
# Demand Media
# 
# All in one processing script that reads the raw data files and
# produces the by-tld files, as well as JAS categorized data files
#
# Copyright (c) 2013, JAS Global Advisors, LLC.
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
# INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
# BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
# OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
# AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
# WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
###############################################################################

use Getopt::Long;
use Data::Dumper;
use POSIX ":sys_wait_h";
use File::Path qw(make_path);
use File::Find;       # will use to replace system call to find
use Net::IDN::Encode ':all';
use Time::Local;
#use NetPacket::IP;
#use NetPacket::TCP;
#use NetPacket::UDP;
#use DBM::Deep;

$SIG{CHLD} = \&REAPER;

our $VERSION = '$Id: subtld.pl 100 2013-11-26 20:36:11Z kwhite $';

#use PerlIO::gzip;
#use threads;

# bytld entries aren't used.  They used to be, but they are calculated
# now, and assumed to be somewhere in the DSTBASE tree.  I have left
# the definitions in here as a note, in case their use needs to be
# resurrected.  Use case: one user wishes to use processed data in
# another user's directory.

# For 2010, the first row is the official DITL data.  There are other
# datasets available in that year, because lots of DITL captures were
# run, due to the roots being signed.  If you wish to include any of
# the other sets, uncomment the lines.

my %LOC = (
    2013 => { 'date' => 'DITL-20130528',
	      'raw' => '/mnt/oarc-pool2/DITL-20130528/RAW',
	      'bytld' => '/home/roy/gtld/by-tld'},
    2012 => { 'date' => 'DITL-20120417',
	      'raw' => '/mnt/oarc-pool4/DITL-20120417/RAW',
	      'bytld' => '/home/roy/gtld/by-tld'},
    2011 => { 'date' => 'DITL-20110412',
	      'raw' => '/mnt/oarc-pool4/DITL-20110412/RAW',
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    2010 => { 'date' => 'DITL-20100413',
#	      'date' => 'DITL-2010',
	      'raw' => ['/mnt/oarc-pool4/DITL-20100413/RAW',
#			'/mnt/oarc-pool3/DITL-20100112/CLEAN',
#			'/mnt/oarc-pool3/DITL-20100119/CLEAN',
#			'/mnt/oarc-pool3/DITL-20100126/CLEAN',
#			'/mnt/oarc-pool3/DITL-20100323/CLEAN',
#			'/mnt/oarc-pool3/DITL-20100504/RAW',
#			'/mnt/oarc-pool3/DITL-20100525/RAW',
#			'/mnt/oarc-pool3/DITL-20100714/CLEAN',
#			'/mnt/oarc-pool4/DITL-20100209/RAW',
#			'/mnt/oarc-pool4/DITL-20100302/RAW',
		  ],
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    2009 => { 'date' => 'DITL-200903',
#	      'raw' => '/mnt/oarc-pool4/DITL-200903/RAW',
	      'raw' => '/mnt/oarc-pool4/DITL-200903/CLEAN-ROOTS',
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    2008 => { 'date' => 'DITL-200803',
	      'raw' => '/mnt/oarc-pool4/DITL-200803/RAW',
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    2007 => { 'date' => 'DITL-200701',
	      'raw' => '/mnt/oarc-pool3/DITL-200701/RAW',
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    2006 => { 'date' => 'DITL-200601',
	      'raw' => '/mnt/oarc-pool3/DITL-200601/RAW',
	      'bytld' => '/home/kwhite/gtld/by-tld'},
    );

my (%ROOTMAP, %ROOTIP, %ROOTBYIP);
my (%OVERRIDE10, %OVERRIDE13);

my $DNS_OARCBASE = '/mnt/oarc-pool3/collisions';
my $DSTBASE = $ENV{HOME}.'/jas/gtld';

my $MAXPROC = 12;
my $MAXPROC_TCPDUMP = 40;
#my $MAXPROC_TCPDUMP = 1;
my $MAXPROC_SORT = 15;

# Data structures for global TLD/Interisle categorization
my %OLDGTLD;
my %NEWGTLD;
my %INSIP;
my %INXMP;

# Data structures to handle children
my %CHILDREN;
my @STIFFS;

# Globals to configure checks
my $DO_HYPHEN_CHECKS = 0;
my $DO_LDH_CHECKS = 0;
my $DO_LEN_CHECKS = 0;
my $DO_RANDOM_CHECKS = 0;
my $DO_PUNYCODE_CHECKS = 1;

my $DO_RAW_DECODE = 1;

############################################################################### 

main();
 
############################################################################### 

sub REAPER {
    my $stiff;
    while (($stiff = waitpid(-1, &WNOHANG)) > 0) {
        # do something with $stiff if you want
#	delete($CHILDREN{$stiff});
	push(@STIFFS, $stiff);
    }
    $SIG{CHLD} = \&REAPER;                  # install *after* calling waitpid
}

###############################################################################

sub CalcTS {
    my ($date, $time) = @_;

    my $ts;

#2011-04-12 20:54:06.876091

    $date =~ /^(\d{4})-(\d{2})-(\d{2})$/;
    my $year = $1 - 1900;
    my $mon = $2 - 1;
    my $mday = $3;
    $time =~ /^(\d{2}):(\d{2}):(\d{2}).(\d*)$/;
    my $hour = $1;
    my $min = $2;
    my $sec = $3;
    my $msec = $4;

    $ts = timegm( $sec, $min, $hour, $mday, $mon, $year );

#    print "$date|$time -> $ts\n";

    return($ts);
}

###############################################################################

sub GroupRandoms {
    my ($randoms) = @_;

    my ($countall, $countyes);
    $countall = $countyes = 0;

#    print "Before:\n";
#    print Dumper($randoms);

    foreach my $sip (keys(%$randoms)) {
	my ($i1, $i2, $i3);
        foreach my $dt (sort(keys(%{$randoms->{$sip}}))) {
	    foreach my $elem (@{$randoms->{$sip}{$dt}}) {
		$countall++;
		my $elemdt = { };
		$elemdt->{dt} = $dt;
		$elemdt->{elem} = $elem;

		$elem->[11] = "OK";

		$i1 = $i2;
		$i2 = $i3;
		$i3 = $elemdt;
		if ((defined $i1) && (defined $i1->{dt}) &&
		    ($i1->{dt} >= $dt - 30))
		{
		    # We're looking at element 3.  There is an
		    # element 1 who's time is within 30 seconds behind
		    # ours.  Thus, all 3 are in a group.  Mark all 3
		    # as random, and clear them out.
		    $i1->{elem}->[11] = "RANDOM10";
		    $i2->{elem}->[11] = "RANDOM10";
		    $i3->{elem}->[11] = "RANDOM10";
		    $i1 = undef;
		    $i2 = undef;
		    $i3 = undef;
		    $countyes += 3;
		}
	    }
	}
    }
#    print "After: $countyes random out of $countall\n";
#    print Dumper($randoms);
    return($countyes, $countall);
}

###############################################################################

sub CopyAndSub {
    my ($src, $dst_loc, $gtld, $year) = @_;
    my $dst = $dst_loc."/".$gtld.".gz";
    my $dst_log = $dst_loc."/".$gtld."_log.gz";
    my $dst_sld = $dst_loc."/".$gtld."_sld";
    my $dst_dbfilename = $dst_loc."/".$gtld.".db";
    my $dst_log_nocollapse = $dst_loc."/".$gtld."_lognocollapse.gz";
    my $dst_interisle_log = $dst_loc."/".$gtld."_interisle.gz";
    my $droplist;
    my %intsum;

#    print "$src\t$dst\t$gtld\t$year\n";

    my ($use_db, $db);
    if (($year == 2013) && ($gtld eq "home")) { $use_db = 1};
    if (($gtld eq "home") || ($gtld eq "corp")) { return();};

    my $randoms = { };

    # Attempt to use an on-disk database instead of RAM. About 3
    # orders of magnitude too slow.  Would need to write something
    # much more optimized, and still probably not enough.
#    if ($use_db) {
#	$droplist = DBM::Deep->new($dst_dbfilename);
#    }
#    else {
	$droplist = { };
#    }

    open(IN, "gunzip -c $src |") || die "ERROR; failed to open input file $src: $!";
    open(my $out, "| gzip -c > $dst") || die "ERROR: failed to open output file $dst: $!";
    while(<IN>) {
	my ($scrub, $interisle, $retrow, $qstr, $sld, $elem) = 
	    ScrubAndInterisle($_);
	if (!defined $scrub) { next; }
	if ($scrub eq "RANDOM10") {
	    my $date = $elem->[0];
	    my $time = $elem->[1];
	    my $sip = $elem->[6];
#	    my $scrub = $elem->[11];
#	    my $qstr = $elem->[13];
#	    my $sld = $elem->[3];

	    # Remove final .sourceport
#	    print "sip: $sip -> ";
	    substr($sip, rindex($sip, ".")) = "";
#	    print "$sip\n";

#2011-04-12 20:54:06.876091
	    my $dt = CalcTS($date, $time);

	    push(@{$randoms->{$sip}{$dt}}, $elem);
	}
	else {
	    addToDrop($droplist, $scrub, $qstr, $sld);
	    $intsum{$interisle}++;
	    print $out $retrow."\n";
	}
    }
    close(IN);

    my ($randyes, $randtot) = GroupRandoms($randoms);
    foreach my $sip (keys(%$randoms)) {
	foreach my $dt(sort(keys(%{$randoms->{$sip}}))) {
	    foreach my $elem (@{$randoms->{$sip}{$dt}}) {
		my $scrub = $elem->[11];
		my $interisle = $elem->[12];
		my $qstr = $elem->[13];
		my $sld = $elem->[3];
		my $retrow = join(" ", @$elem);
		addToDrop($droplist, $scrub, $qstr, $sld);
		$intsum{$interisle}++;
		print $out $retrow."\n";
	    }
	}
    }

    close($out);
    print "$gtld: random: $randyes out of $randtot\n";

    # Create two summary files.  $dst_log_nocollapse just has one row
    # per qstr, with a count, sorted by sld.  $dst_log is more
    # difficult.  Start with an SLD.  A row is present in this file if
    # there were any _valid_ queries to a name in that SLD.  If all of
    # the queries present were invalid, or random, the SLD is removed
    # from the list.

    open(my $outlog, "| gzip -c > $dst_log") || die "ERROR: failed to open output file $dst_log: $!";
    open(my $outlogsld, ">$dst_sld") || die "ERROR: failed to open output file $dst_sld: $!";
    open(my $outlog2, "| gzip -c > $dst_log_nocollapse") || die "ERROR: failed to open output file $dst_log_nocollapse: $!";
    foreach my $sld (sort(keys(%$droplist))) {
	if ($droplist->{$sld}{valid})
	{
	    # If {valid} exists, or is > 0, that means there was at least
	    # one OK query for this sld

	    # That means, we want to print it out, because it was a problem.
	    # Print out the total count of queries for that sld.

	    print $outlog "OK"." ".$sld." ".
		$droplist->{$sld}{valid}."\n";
	    print $outlogsld $sld."\n";
	}
	foreach my $section (sort(keys(%{$droplist->{$sld}{scrubs}}))) {
#	print $outlog $section."\n";
	    my $query;
	    foreach my $query (sort keys(%{$droplist->{$sld}{scrubs}{$section}})) {
		print $outlog2 $section." ".$query." ".
		    $sld." ".
		    $droplist->{$sld}{scrubs}{$section}{$query}{count}."\n";
	    }
	}
    }
    close($outlog);
    close($outlog2);
    close($outlogsld);

    open(my $outlog, "| gzip -c > $dst_interisle_log") || die "ERROR: failed to open output file $dst_interisle_log: $!";
    foreach my $i (sort(keys(%intsum))) {
	print $outlog "$i $intsum{$i}\n";
    }

    close($outlog);
}

###############################################################################

sub ScrubAndInterisle 
{
    my ($src) = @_;

#    binmode STDOUT, ":encoding(utf8)";

    chomp($src);
    my $interisle = "INNONE";
    my $scrub = "OK";
    my @elem = split(/ /, $src);
#($date, $time, $gtld, $sld, $filenum, $protocol, "$sip.$sport", "$dip.$dport", $root, $type, $namelen, $name);
#OLD###2011-04-12 20:54:06.876091 gree blog a-root 119.63.192.232 198.41.0.4 blog.gree
    my $gtld = $elem[2];
    my $root = $elem[8];
    if ((!defined $root) || ($root eq "")) {
	# This only happened due to an earlier bug in the raw stage.
	# It shouldn't happen in future runs.
#	print "no root: $_\n";
	return(undef);
    }
    my $qstr = $elem[11];
    my $qstrlen = $elem[10];
    my @labels = split(/\./, lc($qstr));
    my %labels;
    foreach my $l (@labels) { $labels{$l}++; }
    my $labelcount = scalar(@labels);
    my $sld = ($labelcount >= 2) ? ($labels[$labelcount - 2]) : undef;
    my $flabel = $labels[0];    # "first label"
    
    # Interisle categories

    if ($OLDGTLD{$sld}) {
	$interisle = "INCATB";
    }
    elsif ($NEWGTLD{$sld}) {
	$interisle = "INCATC";
    }
    elsif ((length($sld) == 10) && ($sld =~ /^[a-z]*$/)) {
	$interisle = "INCATD";
    }
    elsif (lc($qstr) eq "www.$gtld") {
	$interisle = "INCATE";
    }
    elsif (($flabel eq "_ldap") || ($flabel eq "_kerberos")) {
	$interisle = "INCATF";
    }
    elsif (defined $labels{"_dnssd"}) {
	$interisle = "INCATG";
    }
    elsif (substr($flabel, 0, 10) eq "File moved") {
	$interisle = "INCATH";
    }
    elsif ($INSIP{$flabel}) {
	$interisle = "INCATI";
    }
    elsif ($INXMP{$flabel}) {
	$interisle = "INCATJ";
    }
    elsif (($flabel eq "mail") || ($sld eq "mail")) {
	$interisle = "INCATK";
    }
    elsif (!defined $sld) {
	$interisle = "INCATL";
    }

    # Various validity checks

    my $scrubbed;

    if ($DO_LEN_CHECKS) {
	if ($qstrlen > 253) {
	    $scrub = "INVALID";
	    $scrubbed++;
	}
	if (!$scrubbed && defined $sld) {
	    if (length($sld) < 3) {
#		print "SHORTSLD: $qstr\n";
		$scrub = "SHORTSLD";
		$scrubbed++;
	    }
	}
    }

    if (!$scrubbed && (substr($sld, 0, 4) eq 'xn--') && ($DO_PUNYCODE_CHECKS)) {
	my $unic;
	eval {
	    $unic = domain_to_unicode($sld);
	};
	if ($@) {
	    # There was an error
	    $scrub = "INVALIDPUNYCODE";
	    print "INVALIDPUNYCODE: $sld -> $@\n";
	    $scrubbed++;
	}
	else {
#	    print "VALIDPUNYCODE: $sld -> $unic\n";
	}
    }

    if ($DO_LDH_CHECKS) {
	if (!$scrubbed && defined $sld) {
	    # If sld has any invalid characters
#	    elsif ($sld =~ /[^a-zA-Z0-9\-]/) {
	    if ($sld =~ /[^a-zA-Z0-9\-]/) {
		$scrub = "INVALID";
		$scrubbed++;
	    }
	    elsif ((substr($sld, 2, 2) eq "--") &&
		   (substr($sld, 0, 2) ne "xn")) {
#		print "INVALIDDASH $qstr\n";
		$scrub = "INVALID";
		$scrubbed++;
	    }
	    # If sld starts or ends with a hyphen
	    elsif ((substr($sld, 0, 1) eq "-") ||
		   (substr($sld, -1, 1) eq "-")) {
		$scrub = "INVALID";
		$scrubbed++;
	    }
	}
    }    
    
    if ($DO_HYPHEN_CHECKS) {
	# Walk through the labels, look for any that start or end with a
	# hyphen.
	if (!$scrubbed) {
	  LABELWALK: foreach my $label (@labels) {
	      if ((substr($label, 0, 1) eq "-") ||
		  (substr($label, -1, 1) eq "-")) {
		  
		  $scrub = "INVALID";
		  $scrubbed++;
		  last LABELWALK;
	      }
#	  else {
	      # Commented out, because this shouldn't be
	      # possible.  The labels have to come from a DNS
	      # packet.  The DNS packets can't hold labels > 63
	      # characters.  So, only corrupt TCPDUMP output
	      # could cause this to happen.  Not worth the
	      # calculation.
	      # Same ^ sub code as above.
#	      my $labellen = $label;
#	      $labellen =~ s/\^\^/\$/g;
#	      $labellen =~ s/\^//g;
#	      
#	      if (length($labellen) > 63)) {
#	      
#	      $scrub = "INVALID";
#	      $scrubbed++;
#	      last LABELWALK;
#	  }
	  }
	}
    }
    
    if ($DO_RANDOM_CHECKS) {
	# Look for 10/13 character random
	if (!$scrubbed) {
	    if ((length($flabel) == 10) && (!$OVERRIDE10{$flabel})) {
		# If it only consists of a-z, we consider it "random" 
		if ($flabel =~ /^[a-zA-Z]*$/) {
		    $scrub = "RANDOM10";
		    $scrubbed++;
		}
	    }
#	    elsif ((length($flabel) == 13) && (substr($flabel, 0, 4) ne "xn--") && (!$OVERRIDE13{$flabel})) {
#		# If it starts with a-z and contains a digit, we consider it "random"
#		# can contain dashes.  Mostly only see up to 2, but this regexp 
#		# allows any number.  Also, if it starts with "xn--", is isn't random.
#		# That check was needed when dashes were added.
#		if ($flabel =~ /^[a-z][a-z0-9\-]*[0-9][a-z0-9\-]*$/) {
#		    $scrub = "RANDOM13";
#		    $scrubbed++;
#		}
#	    }
	}
    }
    $elem[11] = $scrub;
    $elem[12] = $interisle;
    $elem[13] = $qstr;
    my $retrow = join(" ", @elem);

    return($scrub, $interisle, $retrow, $qstr, $sld, \@elem);
}

###############################################################################

sub addToDrop {
    my ($droplist, $scrub, $string, $sld) = @_;

    # Maintain the droplist.  By sld, store :
    # {valid} count of valid queries
    # {invalid} count of invalid queries
    # {scrubs} a hash, by scrub type, of each string that was removed,
    # and the count.

    $droplist->{$sld}{scrubs}{$scrub}{$string}{count}++;
    if ($scrub eq "OK") {
	$droplist->{$sld}{valid}++;
    }
    else {
	$droplist->{$sld}{invalid}++;
    }
}
 
############################################################################### 

sub VerifySrc {
    my ($src) = @_;

    my @src;
    if (ref($src) eq "ARRAY") {
	@src = @$src;
    }
    else {
	@src[0] = $src;
    }

    # A source should exist and be a directory

    my $badcount;

    foreach my $src (@src) {
	if (!-d $src) {
	    print "Source $src is not a directory.\n";
	    $badcount++;
	}
    }
    return ($badcount);
}

############################################################################### 

sub VerifyDst {
    my (@dst) = @_;

    # A destination shouldn't exist.  Make it, verify that it then
    # does exist.

    my $badcount;

    foreach my $dst (@dst) {
	if (-d $dst) {
	    print "Destination $dst already exists.\n";
	    $badcount++;
	    next;
	}
	make_path($dst, {error => \my $err});
	if (@$err) {
	    for my $diag (@$err) {
		my ($file, $message) = %$diag;
		if ($file eq '') {
		    print "general error: $message\n";
		}
		else {
		    print "problem mkdir'ing $file: $message\n";
		}
	    }
	}
	if (!-d $dst) {
	    print "Desgination $dst was not created.\n";
	    $badcount++;
	}
    }
    if ($badcount) { exit(3); }
}

############################################################################### 

sub CalcSrcDst {
    my ($year, $suffix, $jassuffix, $systemwide_archive) = @_;

    my ($raw, $intermediate, $bytld, $jas);

    $raw = $LOC{$year}{raw};
    
    my $mydstbase = ($systemwide_archive) ? $DNS_OARCBASE : $DSTBASE;

    $intermediate = $mydstbase."/intermediate/".$LOC{$year}{date}."-".$suffix;
    $bytld = $mydstbase."/by-tld/".$LOC{$year}{date}."-".$suffix;
    $jas = $DSTBASE."/jas/".$LOC{$year}{date}."-".$suffix;
    $jas .= "-".$jassuffix if defined $jassuffix;

    return($raw, $intermediate, $bytld, $jas)
}

############################################################################### 

sub FindRawFiles {
    my ($year, $map, $src_in) = @_;

    my @src;
    if (ref($src_in) eq "ARRAY") {
        @src = @$src_in;
    }
    else {
        @src[0] = $src_in;
    }
    
    my $rawFiles = [ ];

#    print Dumper($map);
    foreach my $root (sort(keys(%$map)))
    {
	foreach my $src (@src)
	{
	    my $locref = $map->{$root}{loc};
	    my @loc;
	    if (ref($locref) eq "ARRAY") {
		@loc = @$locref;
	    }
	    else {
		@loc[0] = $locref;
	    }
	    foreach my $loc (@loc) {
		my $cmd = "find \"$src/$loc\" -type f";
		print "$cmd\n";
		my @output = qx/$cmd/;
		foreach my $line (@output) {
		    chomp $line;
		    my %file;
		    $file{root} = $root;
		    $file{src} = $line;
		    
		    # Calculate a destination name for the intermediate file.
		    # Start past the root, and replace all / by _ to flatten
		    # out the filename/directory structure
		    
		    my $dst = substr($line, index($line, $root) + length($root) + 1);
		    $dst =~ s/\//_/g;
		    $file{dst} = $dst;
		    push(@$rawFiles, \%file);
#		    print Dumper(\%file);
		}
	    }
	}
    }
    return($rawFiles);
}

############################################################################### 

sub DumpRawMap {
    my ($rawFiles, @dsts) = @_;

    foreach my $dst (@dsts) {
	my $ofile = $dst."/pcapmap";
	open(OUT, ">$ofile") || die "ERROR failed to open output file $ofile: $!";

	my $i = 0;
	foreach my $file (@$rawFiles) {
	    print OUT $i++." ".$file->{src}."\n";
	}
	close(OUT);
    }
}

############################################################################### 

sub ParseRawFiles {
    my ($rawFiles, $dst, $bytld_dst) = @_;

    my $sleeptime = 0;
    my $qlen = scalar(@$rawFiles);
    my $i = 0;
    
    while ($qlen > 0) {
	while (scalar(keys(%CHILDREN)) >= $MAXPROC_TCPDUMP) { 
	    while (@STIFFS) {
		my $stiff = shift(@STIFFS);
		delete($CHILDREN{$stiff});
	    }
	    sleep(5); 
	}
	my $file = shift(@$rawFiles);
	
	my $pid = fork();
	if ($pid) {
	    # parent
	    $CHILDREN{$pid}++;
	}
	elsif ($pid == 0) {
	    # child

#	    print "ChildStart: $qlen $file\n";
	    my $fulldest = $dst."/".$file->{root};
	    make_path($fulldest);
	    make_path($bytld_dst);
	    DumpPcap($file->{src}, $fulldest."/".$file->{dst}, $bytld_dst, $i);
#	    print "ChildEnd: $file\n";
	    exit(0);
	}
	
	$qlen = scalar(@$rawFiles);
	$i++;
    }
    while (scalar(keys(%CHILDREN)) > 0) { 
	while (@STIFFS) {
	    my $stiff = shift(@STIFFS);
	    delete($CHILDREN{$stiff});
	}
	sleep(5); 
    }
}

###############################################################################

sub findOffset {
    my ($data, $linktype) = @_;

    my $debugout = 0;

    # Start with a packet from tcpdump, starting with the Ethernet
    # Frame past the Premable.  (Not sure why I didn't get the
    # preamble when I did -XX, but I didn't.)  Look for the EtherType
    # of 8100 to detemine if we need to jump over the VLAN tag.  Then,
    # decipher IPv4 or IPv6, then TCP or UDP, to get to the DNS
    # packet, then find the start of the name.
    
    my $protocol;
    my $offset = 12;
    my $skipip;
    my ($ip_verlen, $ip_ver);

    if ($linktype == 1) {
	my $ethertype = ($data->[$offset] * 256) + $data->[$offset + 1];
	if (($ethertype == 0x8100) || ($ethertype == 0x0800) ||
	    ($ethertype == 0x86dd)) {
	    $offset += 2;
	    $offset += 4 if ($ethertype == 0x8100);
	}
	else {
	    printf("ethertype %04x unknown\n", $ethertype) if $debugout;
	    return(-1);
	}
    }
    elsif ($linktype == 101) {
	print "linktype $linktype nolink " if $debugout;
	$offset = 0;
	$ip_verlen = $data->[$offset];
	$ip_ver = ($ip_verlen & (128 + 64 + 32 + 16)) >> 4;
	if (($ip_ver == 4) || ($ip_ver == 6)) {
	    $skipip++;
	    print "$offset: $ip_verlen ip_ver: $ip_ver " if $debugout;
	}
	else {
	    return(-1);
	}
    }
    elsif ($linktype == 108) {
	print "linktype $linktype OpenBSD skip 4 " if $debugout;
	$offset = 4;
	$ip_verlen = $data->[$offset];
	$ip_ver = ($ip_verlen & (128 + 64 + 32 + 16)) >> 4;
	if (($ip_ver == 4) || ($ip_ver == 6)) {
	    $skipip++;
	    print "$offset: $ip_verlen ip_ver: $ip_ver " if $debugout;
	}
	else {
	    return(-1);
	}
    }
    else {
	print "linktype $linktype UNKNOWN nolink " if $debugout;
	$offset = 0;
	$ip_verlen = $data->[$offset];
	$ip_ver = ($ip_verlen & (128 + 64 + 32 + 16)) >> 4;
	if (($ip_ver == 4) || ($ip_ver == 6)) {
	    $skipip++;
	    print "$offset: $ip_verlen ip_ver: $ip_ver " if $debugout;
	}
	else {
	    return(-1);
	}
    }

    if (!$skipip) {
	$ip_verlen = $data->[$offset];
	$ip_ver = ($ip_verlen & (128 + 64 + 32 + 16)) >> 4;
	print "$offset: $ip_verlen ip_ver: $ip_ver " if $debugout;
    }
    if ($ip_ver == 6) {
	my $next_header = $data->[$offset + 6];
	print "next_header: $next_header " if $debugout;
	$offset += 40;
	while (!(($next_header == 6) || ($next_header == 17))) {
	    $next_header = $data->[$offset + 0];
	    $offset += 8 + (8 * $data->[$offset + 1]);
	    last if $offset > 9000;
	}
	if ($next_header == 6) { $protocol = "tcp";}
	elsif ($next_header == 17) { $protocol = "udp"; }
	print "$offset " if $debugout;
    }
    elsif ($ip_ver == 4) {
	my $ip_len = ($ip_verlen & (8 + 4 + 2 + 1));
	print "$ip_verlen -> $ip_len " if $debugout;
	my $prnum = $data->[$offset + 9];
	$offset += (4 * $ip_len);
	if ($prnum == 6) { $protocol = "tcp";}
	elsif ($prnum == 17) { $protocol = "udp"; }
	print "$offset " if $debugout;
    }

    if ($protocol eq "tcp") {
	my $len = $data->[$offset + 12];
	$len = ($len % (128 + 64 + 32 + 16)) >> 4;
	$offset += ($len * 4);
    }
    elsif ($protocol eq "udp") {
	$offset += 8;
    }
    
    # DNS
    $offset += 12;
    $offset += 2 if ($protocol eq "tcp");  # two extra bytes, length

    print "$offset " if $debugout;
    if ($offset > 9000) {
	$offset = -1;
	print " -> $offset" if $debugout;
    }
    print "\n" if $debugout;

    return($offset);
}

###############################################################################

sub getNameFromData {
    my ($data, $linktype) = @_;
    
    # In the case that the tcpdump output has control characters (^
    # and M-) that can't be reversed, go to the actual tcpdump output
    # to resurrect the name

    my ($name, $namelen);

    my $offset = findOffset($data, $linktype);
    if ($offset < 0) {
	print "ERROR: no offset\n";
	return(undef, -1);
    }

    my ($sld, $tld);
    my $i = $offset;
    my $labelcount = 0;
    my $labellen = $data->[$i];
    while ((defined $labellen) && ($labellen > 0)) {
	$labelcount++;
	my $label;
	if ($labelcount > 127) {
	    print "ERROR: too many labels\n";
	    return(undef, -2);
	}
	my $flags = $labellen & (128 + 64);
	$labellen = $labellen & (32 + 16 + 8 + 4 + 2 + 1);
	if ($flags > 0) {
	    print "ERROR: label length ".$data->[$i]." has flags set.\n";
	    return(undef, -3);
	}
	foreach (my $count = 0; $count < $labellen; $count++) {
	    # before now, $i is pointing at the labellen.  move past.
	    $i++;
	    my $char = $data->[$i];
	    $namelen++;
	    # char 32 is the space, so space and below
	    # 46 is .
	    # 92 is \
	    # 127 is DEL, above is undefined in ASCII
	    if (($char < 33) || ($char == 46) || ($char == 92) ||
		($char > 126)) {
		$name .= '\\'.sprintf("%02x", $char);
		$label .= '\\'.sprintf("%02x", $char);
	    }
	    else {
		$name .= pack("C", $char);
		$label .= pack("C", $char);
	    }
	}
	$sld = $tld;
	$tld = $label;
	$i++;
	$labellen = $data->[$i];
	# $labellen is now holding the length of the _next_ label.
	# Cheat here and check to see if that's 0.  If it isn't, add
	# the "." label separator to our name.
	if ($labellen != 0) {
	    $name .= ".";
	    $namelen++;
	}
    }
    if (!defined $labellen) {
	# We broke out of the loop becaose we walked past the end of
	# the byte array, which means something wasn't right.
	print "ERROR: got to end of data.\n";
	return(undef, -4);
    }
    
    return($name, $namelen, $sld);
}

###############################################################################

sub DumpPcap {
    my ($src, $dst, $bytld_dst, $filenum) = @_;

    open(my $outlog, "| gzip -c > $dst") || die "ERROR failed to open output file $dst: $!";
#    print "gunzip -dc \"$src\" | tcpdump -tttt -X -n -s 0 -r -\n";
    
    my $gzip = ($src =~ /\.gz$/);
    
    my $IN;
    if ($gzip) {
	open($IN, "gunzip -c $src|") || die "ERROR failed to open input file and tcpdump $src: $!";
    }
    else {
	open($IN, $src) || die "ERROR failed to open input file and tcpdump $src: $!";
    }

    my $hdr;
    sysread($IN, $hdr, 24); 
    my ($magic, $maj, $min, $off, $acc, $snaplen, $linktype) = unpack("LSSLLLL", $hdr); 
#    print "linktype: $linktype\n";
    close($IN);

    my $raw_option = ($DO_RAW_DECODE) ? "-XX" : "";
    if ($gzip) {
	open($IN, "gunzip -dc \"$src\" | tcpdump -tttt $raw_option -n -s 0 -r - 2> /dev/null |") || die "ERROR failed to open input file and tcpdump $src: $!";
    }
    else {
	open($IN, "/usr/sbin/tcpdump -tttt $raw_option -n -s 0 -r \"$src\" 2> /dev/null |") || die "ERROR failed to open input file and tcpdump $src: $!";
    }
    my %files;

#    gunzip -dc "$infile" | tcpdump -n -s 0 -r - 2> /dev/null | ./filter-tcpdump-tldlist.pl $tldlist | gzip -6 > $outname.gz
#14:19:59.081577 IP6 2a02:2098:8711:8c21:0:2:b19:b00b.24372 > 2001:503:ba3e::2:30.53: 23630 [1au] A? www.hybridtraffic.com.home. (55)
#2013-05-29 14:19:59.081577 IP6 2a02:2098:8711:8c21:0:2:b19:b00b.24372 > 2001:503:ba3e::2:30.53: 23630 [1au] A? www.hybridtraffic.com.home. (55)
#2013-10-17 15:33:28.813057 IP 192.168.10.40.43000 > 192.168.10.250.53: Flags [P.], seq 0:45, ack 1, win 229, options [nop,nop,TS val 174806473 ecr 3132314737], length 4557684+ [1au] A? mail.kevbo.org. (43)
    my $parseRawName = 0;
    my @rawline;
    my @rawdata;

    while (<$IN>) {
#	print "$_";
	
	if (substr($_, 0, 3) eq "\t0x") {
	    # Line is raw data
	    # Snarf it up, don't do anything else with it.
	    if ($parseRawName) {
#		print $_;
#	0x0000:  4500 003c 3532 4000 4006 6f17 c0a8 0a28  E..<52@.@.o....(
		# First byte is at pos 10.
		my $pos = 10;
		for (my $i = 0; $i < 16; $i++) {
		    my $chrs = substr($_, $pos, 2);
#		    print "$chrs\n";
		    push(@rawdata, hex($chrs));
		    $pos += 2;
		    if (($i % 2) == 1) { $pos ++; }
		}
	    }
	    next;
	}

	if ($parseRawName) {
	    # We _were_ in $parseRawName.  This line isn't raw data.
	    # Thus, we are done, and should finish our row and print
	    # it out.  Oh, and then process the current line.

	    my $origname = pop(@rawline);
	    my $tld = pop(@rawline);
	    my $protocol = $rawline[5];
	    my $dip = $rawline[7];
	    my $ipv = 4;
	    if (index($dip, ':') != -1) {
		# if the destination IP had a :, it is ipv6
		$ipv = 6;
	    }
	    my ($name, $namelen, $sld) = getNameFromData(\@rawdata, $linktype);
	    if ($namelen < 0) {
		print "RAWSKIP: INVALIDRAWNAME: $filenum: ".$rawline[4]." ".$origname." ".$rawline[6]." ".$rawline[7]."\n";
	    }
	    else {
		push (@rawline, $namelen, lc($name));
		$rawline[3] = lc($sld);
		
		print $outlog (join " ", @rawline)."\n";
#		print "Finished raw: ".(join " ", @rawline)."\n";
		my $file = $tld;
		if (!defined $files{$file}) {
		    #$files{$file} = new IO::Compress::Gzip "$outdir/$file" || die "gzip failed: $GzipError";
		    open(my $fh, ">>", "$bytld_dst/$file") || die "ERROR: failed to open for $tld: $!";
		    $files{$file} = $fh;
		}
		my $fh = $files{$file};
		syswrite $fh, (join " ", @rawline)."\n";
	    }
	    
	    $parseRawName = 0;
	}
	
	my $rawskip;
	my $protocol = 'udp';
	# The query is at the end.  It ends with the final ".".  It
	# starts past the ? in the query type.  If you can't find a ?
	# followed by a space, then this isn't a valid query row.
	# Look for the first "? " string, because, in theory "? " is
	# actually a valid part of a domain name
	my $nameend = rindex($_, ".");
	my $namestart = index($_, "? ");
	if ($namestart == -1)
	{
	    $rawskip++;
	}
	my $name = substr($_, $namestart+2, $nameend-$namestart-2);
	$name = lc($name);

        my $tldstart = rindex($name, ".");
        next if $tldstart == -1;
        my $tld = substr($name, $tldstart+1);
        next unless defined $NEWGTLD{$tld};
#	print "i care: :$tld:\n";

	my $namelen = length($name);
	# Replace all \ with \5c
	# Replace all spaces with \20
	# If any ^ or m- are found, will go into binary mode and do
	# the whole string.
	$name =~ s|\\|\\5c|g;
	$name =~ s| |\\20|g;

	my $typestart = rindex($_, " ", $namestart-1);
	# -1 removes the ? at the end
	my $type = substr($_, $typestart+1, $namestart-$typestart-1);
	my @parts = split(/ /, $_, 7);

	if (substr($parts[6], 0, 7) eq "Flags [") {
	    $protocol = "tcp";
#	    print $_;
	}
	if ($rawskip) {
	    # OK, so, we didn't find a name server query.  If this
	    # query is TCP with a length of 0, , we can silently drop
	    # the NOMATCH, because it is a fragment.
	    if ($protocol eq "tcp") {
		if (substr($_, -7) eq "length 0") {
		    # TCP fragment.  Skip silently
		    next;
		}
	    }
	}

	my $date = $parts[0];
	my $time = $parts[1];

	# Handle GREv0: use the second set of sip/dip
	my ($sip, $dip);
	if ($parts[6] eq "GREv0") {
	    $sip = $parts[10];
	    $dip = $parts[12];
	}
	else {
	    $sip = $parts[3];
	    $dip = $parts[5];
	}

        my $sipe = rindex($sip, ".");
	my $sport = substr($sip, $sipe + 1);
        substr($sip, $sipe) = "";
        my $dipe = rindex($dip, ".");
	my $dport = substr($dip, $dipe + 1);
	chop($dport);  # has an extra : on the end
        substr($dip, $dipe) = "";
	my $root = $ROOTBYIP{$dip};
	if ($dport != 53) {
	    # The destination port isn't 53.
#	    print "RAWSKIP: DPORTNOT53: $filenum: $_";
	    next;
	}
	if (!defined $root) {
	    # The destination IP address doesn't match any known root
	    # address, so we're going to ignore this row.
	    print "RAWSKIP: NONROOT: $filenum: $_";
	    next;
	}
	if ($rawskip) {
	    print "RAWSKIP: NOMATCH: $filenum: $_";
	    next;
	}

	# Split the name into parts based on .  Pop off the final .
	# Pop off the next to get the SLD.  Use "." for the SLD if
	# there wasn't one.
        my @dom_parts = split(/\./, $name);
        pop @dom_parts;
        my $sld = pop @dom_parts || ".";
	
	my @outdata = ($date, $time, $tld, $sld, $filenum, $protocol,
		       "$sip.$sport", "$dip.$dport", $root, $type);
	if (($DO_RAW_DECODE) && ((index($name, '^') != -1) || (index($name, 'm-') != -1))) {
	    # String has binary data.  Go into raw mode;
	    $parseRawName = 1;
	    @rawline = @outdata;
	    push(@rawline, $tld, $name);
	    undef (@rawdata);
#	    print "Going raw: $name\n";
#	    print $_;
	}
	else {
	    push(@outdata, $namelen, $name);
	    print $outlog (join " ", @outdata)."\n";
	    
	    my $file = $tld;
	    if (!defined $files{$file}) {
		#$files{$file} = new IO::Compress::Gzip "$outdir/$file" || die "gzip failed: $GzipError";
		open(my $fh, ">>", "$bytld_dst/$file") || die "ERROR: failed to open for $tld: $!";
		$files{$file} = $fh;
	    }
	    my $fh = $files{$file};
	    syswrite $fh, (join " ", @outdata)."\n";
	}
    }
    close($outlog);
    close($IN);
    %files = (); # close everything
}

############################################################################### 

sub SortByTld {
    my ($dir) = @_;

    opendir(DIR, $dir);
    my @files = readdir(DIR);
    closedir(DIR);

    my $qlen = scalar(@files);

    # The SIGCHLD signal handler was catching too many children and
    # decrementing the process count too much, so I'm doing it
    # differently now.  I maintain a hash of all of my child
    # processe.  The signal handler adds the pid of the reaped child
    # to a simple list.  Here, I loop through that list (when I think
    # I have too many children running) and remove those pids from my
    # hash.  The result will be a hash that contains just the
    # currently running pids, and I can know how many more processes I
    # can start.
    
    while ($qlen > 0) {
	while (scalar(keys(%CHILDREN)) >= $MAXPROC_SORT) { 
	    while (@STIFFS) {
		my $stiff = shift(@STIFFS);
		delete($CHILDREN{$stiff});
	    }
	    sleep(5); 
	}
	my $file = shift(@files);
	my $fpath = "$dir/$file";
	next if (!-f $fpath);
	print "Parent ($$) starting child for $qlen $file\n";
	
	my $pid = fork();
	if ($pid) {
	    # parent
	    $CHILDREN{$pid}++;
	}
	elsif ($pid == 0) {
	    # child

	    print "ChildStart ($$): $qlen $file\n";
	    my $cmd = "sort -S25G -k4 -o $fpath $fpath";
	    system($cmd);
	    print "ChildEnd ($$): $file\n";
	    exit(0);
	}
	
	$qlen = scalar(@files);
    }
    while (scalar(keys(%CHILDREN)) > 0) { 
	while (@STIFFS) {
	    my $stiff = shift(@STIFFS);
	    delete($CHILDREN{$stiff});
	}
	sleep(5); 
    }
    
#    my $cmd = "echo $dir/* | xargs -P15 -n 1 -I % 
#    print "$cmd\n";
#    system($cmd);
}

############################################################################### 

sub CompressByTld {
    my ($dir) = @_;

    chdir($dir);
    my $cmd = "echo * | xargs -P10 pigz";
    print "$cmd\n";
    system($cmd);
}

############################################################################### 

sub Usage {
    print "subtld.pl --year YEAR --suffix SUFFIX [--raw] [--jas] [--single tldname]\n";
    print "          [--jassuffix SUFFIX]\n";
    print "          [--ldh | --noldh] [--len | --nolen]\n";
    print "          [--random | --norandom] [--hyphen | --nohyphen]\n";
    print "          [--punycode | --nopunycode]\n\n";
    print "          --jassuffix: suffix used for destination in JAS pass\n";
    print "          --raw: do processing of RAW data\n";
    print "          --jas: do processing of JAS summarization\n";
    print "          (Without --raw or --jas, nothing will be done.)\n";
    print "          --ldh: do checks for LDH at SLD\n";
    print "          --len: do length checks: entire string, SHORTSLD\n";
    print "          --random: do checks for random at left-most label\n";
    print "          --hyphen: do checks for trailing/leading hyphens at all levels\n";
}

############################################################################### 

sub main {
    populateRootMap();
    populateTlds();
    populateOverrides();
 
    my ($single);
    my @files;

    my $doRaw;
    my $doJAS;

    my ($year, $suffix, $jassuffix);

    GetOptions("single=s" => \$single,
	       'suffix=s' => \$suffix,
	       'jassuffix=s' => \$jassuffix,
	       'year=i' => \$year,
	       'raw' => \$doRaw,
	       'jas' => \$doJAS,
	       'ldh!' => \$DO_LDH_CHECKS,
	       'len!' => \$DO_LEN_CHECKS,
	       'punycode!' => \$DO_PUNYCODE_CHECKS,
	       'random!' => \$DO_RANDOM_CHECKS,
	       'hyphen!' => \$DO_HYPHEN_CHECKS,
	);
    if (!defined $year) {
	Usage();
	exit(1);
    }
    if (!defined $suffix) {
	Usage();
	exit(1);
    }
    if (!$doRaw && !$doJAS) {
	Usage();
	exit(1);
    }
    my ($raw, $intermediate, $bytld, $jas) = CalcSrcDst($year, $suffix, $jassuffix, 0);
    
    if ($doRaw)
    {
	if (VerifySrc($raw) != 0) {
	    exit(2);
	}
	VerifyDst($intermediate, $bytld);
	my $rawFiles = FindRawFiles($year, $ROOTMAP{$year}, $raw);
	DumpRawMap($rawFiles, $intermediate, $bytld);
	ParseRawFiles($rawFiles, $intermediate, $bytld);
	SortByTld($bytld);
	CompressByTld($bytld);
    }
	
    if ($doJAS)
    {
	print "Trying $bytld for source\n";
	if ($year ne "all") {
	    if (VerifySrc($bytld) != 0 ) {
		($raw, $intermediate, $bytld, $jas) = CalcSrcDst($year, $suffix, $jassuffix, 1);
		print "Trying $bytld for source\n";
		if (VerifySrc($bytld) != 0) {
		    exit(2);
		}
	    }
	    VerifyDst($jas);
	}

	print "Do full label hyphen checks\n" if ($DO_HYPHEN_CHECKS);
	print "Do SLD LDH character checks\n" if ($DO_LDH_CHECKS);
	print "Do length checks (full name, SHORTSLD)\n" if ($DO_LEN_CHECKS);
	print "Do RANDOM checks\n" if ($DO_RANDOM_CHECKS);
	print "Do valid Punycode checks\n" if ($DO_PUNYCODE_CHECKS);

	my @files2;
	if (defined $single) { 
	    my $file = $single;
	    if ($file =~ /^(.*).gz$/) {
		my %procfile;
		$procfile{filename} = $file;
		$procfile{src} = $bytld;
		$procfile{dst} = $jas;
		$procfile{year} = $year;
		
		push(@files2, \%procfile);
	    }
	}
	else {
	    opendir(DIR, $bytld);
	    my @files = readdir(DIR);
	    closedir(DIR); 
	    foreach my $file (@files) {
		if ($file =~ /^(.*).gz$/) {
		    my %procfile;
		    $procfile{filename} = $file;
		    $procfile{src} = $bytld;
		    $procfile{dst} = $jas;
		    $procfile{year} = $year;
			
		    push(@files2, \%procfile);
		}
	    }
	}
	runCopyAndSub(\@files2);
    }
}
 
############################################################################### 

sub runCopyAndSub {
    my ($files) = @_;
    my $sleeptime = 0;
    my $qlen = scalar(@$files);

    # The SIGCHLD signal handler was catching too many children and
    # decrementing the process count too much, so I'm doing it
    # differently now.  I maintain a hash of all of my child
    # processe.  The signal handler adds the pid of the reaped child
    # to a simple list.  Here, I loop through that list (when I think
    # I have too many children running) and remove those pids from my
    # hash.  The result will be a hash that contains just the
    # currently running pids, and I can know how many more processes I
    # can start.
    
    while ($qlen > 0) {
	while (scalar(keys(%CHILDREN)) >= $MAXPROC_TCPDUMP) { 
	    while (@STIFFS) {
		my $stiff = shift(@STIFFS);
		delete($CHILDREN{$stiff});
	    }
	    sleep(5); 
	}
	my $procfile = shift(@$files);
	my $file = $procfile->{filename};
	my $src = $procfile->{src};
	my $dst = $procfile->{dst};
	my $year = $procfile->{year};
	$file =~ /^(.*).gz$/;
	my $gtld = $1;
	print "Parent ($$) starting child for $qlen $file\n";
	
	my $pid = fork();
	if ($pid) {
	    # parent
	    $CHILDREN{$pid}++;
	}
	elsif ($pid == 0) {
	    # child

	    print "ChildStart ($$): $qlen $file\n";
	    CopyAndSub($src."/".$file,
		       $dst,
		       $gtld,
		       $year);
	    print "ChildEnd ($$): $file\n";
	    exit(0);
	}
	
	$qlen = scalar(@$files);
    }
    while (scalar(keys(%CHILDREN)) > 0) { 
	while (@STIFFS) {
	    my $stiff = shift(@STIFFS);
	    delete($CHILDREN{$stiff});
	}
	sleep(5); 
    }
}

###############################################################################

sub populateOverrides
{
    %OVERRIDE10 = (
	'yourdomain' => 1,
	'boockstore' => 1,
	'fruitsmoke' => 1,
	'musclefood' => 1,
	'changelogs' => 1,
	);
    %OVERRIDE13 = (
	'p12-rout01-pr.3975' => 1,
	);
}

###############################################################################

sub populateTlds
{
    my $tldfile = $ENV{HOME}.'/tools/tlds-all';
    open(IN, $tldfile) || die "ERROR: Unable to open tld file $tldfile: $!";
    while (<IN>) {
	chomp;
	s/^\s+|\s+$//g;
	my $tld = lc($_);
	$NEWGTLD{$tld} = $tld;
    }
    # The empty key seems to sneak its way in.  Remove it.
    delete ($NEWGTLD{undef});
    delete ($NEWGTLD{''});
    
# from http://data.iana.org/TLD/tlds-alpha-by-domain.txt
# Version 2013091101, Last Updated Thu Sep 12 07:07:01 2013 UTC
my @tlds = qw (
AC
AD
AE
AERO
AF
AG
AI
AL
AM
AN
AO
AQ
AR
ARPA
AS
ASIA
AT
AU
AW
AX
AZ
BA
BB
BD
BE
BF
BG
BH
BI
BIZ
BJ
BM
BN
BO
BR
BS
BT
BV
BW
BY
BZ
CA
CAT
CC
CD
CF
CG
CH
CI
CK
CL
CM
CN
CO
COM
COOP
CR
CU
CV
CW
CX
CY
CZ
DE
DJ
DK
DM
DO
DZ
EC
EDU
EE
EG
ER
ES
ET
EU
FI
FJ
FK
FM
FO
FR
GA
GB
GD
GE
GF
GG
GH
GI
GL
GM
GN
GOV
GP
GQ
GR
GS
GT
GU
GW
GY
HK
HM
HN
HR
HT
HU
ID
IE
IL
IM
IN
INFO
INT
IO
IQ
IR
IS
IT
JE
JM
JO
JOBS
JP
KE
KG
KH
KI
KM
KN
KP
KR
KW
KY
KZ
LA
LB
LC
LI
LK
LR
LS
LT
LU
LV
LY
MA
MC
MD
ME
MG
MH
MIL
MK
ML
MM
MN
MO
MOBI
MP
MQ
MR
MS
MT
MU
MUSEUM
MV
MW
MX
MY
MZ
NA
NAME
NC
NE
NET
NF
NG
NI
NL
NO
NP
NR
NU
NZ
OM
ORG
PA
PE
PF
PG
PH
PK
PL
PM
PN
POST
PR
PRO
PS
PT
PW
PY
QA
RE
RO
RS
RU
RW
SA
SB
SC
SD
SE
SG
SH
SI
SJ
SK
SL
SM
SN
SO
SR
ST
SU
SV
SX
SY
SZ
TC
TD
TEL
TF
TG
TH
TJ
TK
TL
TM
TN
TO
TP
TR
TRAVEL
TT
TV
TW
TZ
UA
UG
UK
US
UY
UZ
VA
VC
VE
VG
VI
VN
VU
WF
WS
XN--0ZWM56D
XN--11B5BS3A9AJ6G
XN--3E0B707E
XN--45BRJ9C
XN--80AKHBYKNJ4F
XN--80AO21A
XN--90A3AC
XN--9T4B11YI5A
XN--CLCHC0EA0B2G2A9GCD
XN--DEBA0AD
XN--FIQS8S
XN--FIQZ9S
XN--FPCRJ9C3D
XN--FZC2C9E2C
XN--G6W251D
XN--GECRJ9C
XN--H2BRJ9C
XN--HGBK6AJ7F53BBA
XN--HLCJ6AYA9ESC7A
XN--J1AMH
XN--J6W193G
XN--JXALPDLP
XN--KGBECHTV
XN--KPRW13D
XN--KPRY57D
XN--L1ACC
XN--LGBBAT1AD8J
XN--MGB9AWBF
XN--MGBAAM7A8H
XN--MGBAYH7GPA
XN--MGBBH1A71E
XN--MGBC0A9AZCG
XN--MGBERP4A5D4AR
XN--MGBX4CD0AB
XN--O3CW4H
XN--OGBPF8FL
XN--P1AI
XN--PGBS0DH
XN--S9BRJ9C
XN--WGBH1C
XN--WGBL6A
XN--XKC2AL3HYE2A
XN--XKC2DL3A5EE0H
XN--YFRO4I67O
XN--YGBI2AMMX
XN--ZCKZAH
XXX
YE
YT
ZA
ZM
ZW
);
foreach my $tld (@tlds) {
    $OLDGTLD{lc($tld)} = 1;
}
@tlds = qw (_sip _sipinternal _sipinternaltls _sipfederationtls _sips);
foreach my $tld (@tlds) {
    $INSIP{lc($tld)} = 1;
}

@tlds = qw (_xmppclient _xmppserver _xmpconnect);
foreach my $tld (@tlds) {
    $INXMP{lc($tld)} = 1;
}
}

###############################################################################

sub populateRootMap
{
    %ROOTIP = (
	'a-root' => {
	    'ip' => {
		'198.41.0.4' => 1,
		'2001:503:ba3e::2:30' => 1,
	    }
	},
	'b-root' => {
	    'ip' => {
		'192.228.79.201' => 1,
		'128.9.0.107' => 1,
#		'2001:478:65::53' => 1,
	    }
	},
	'c-root' => {
	    'ip' => {
		'192.33.4.12' => 1,
	    }
	},
	'd-root' => {
	    'ip' => {
		'199.7.91.13' => 1,
		'128.8.10.90' => 1,
		'2001:500:2d::d' => 1,
	    }
	},
	'e-root' => {
	    'ip' => {
		'192.203.230.10' => 1,
	    }
	},
	'f-root' => {
	    'ip' => {
		'39.13.229.241' => 1,
		'192.5.5.241' => 1,
		'2001:500:2f::f' => 1,
		'2001:500::1035' => 1,
		'204.152.184.76' => 1,
	    }
	},
	'g-root' => {
	    'ip' => {
		'192.112.36.4' => 1,
		'192.112.36.2' => 1,
		'192.112.36.1' => 1,
	    }
	},
	'h-root' => {
	    'ip' => {
		'128.63.2.53' => 1,
		'2001:500:1::803f:235' => 1,
	    }
	},
	'i-root' => {
	    'ip' => {
		'192.36.148.17' => 1,
		'2001:7fe::53' => 1,
	    }
	},
	'j-root' => {
	    'ip' => {
		'192.58.128.30' => 1,
		'198.41.0.10' => 1,
		'2001:503:c27::2:30' => 1,
	    }
	},
	'k-root' => {
	    'ip' => {
		'193.0.14.129' => 1,
		'198.41.0.11' => 1,
		'2001:7fd::1' => 1,
	    }
	},
	'l-root' => {
	    'ip' => {
		'199.7.83.42' => 1,
		'198.32.64.12' => 1,
		'2001:500:3::42' => 1,
	    }
	},
	'm-root' => {
	    'ip' => {
		'198.32.65.12' => 1,
		'192.0.6.13' => 1,
		'202.12.27.33' => 1,
		'2001:dc3::35' => 1,
	    }
	},
	);

    foreach my $root (sort(keys(%ROOTIP)))
    {
	foreach my $ip (keys (%{$ROOTIP{$root}{ip}}))
	{
	    $ROOTBYIP{$ip} = $root;
	}
    }
#    print Dumper(\%ROOTBYIP);

    %ROOTMAP = (
	2013 => {
	    'a-root' => {
		'loc' => 'a-root',
	    },
	    'c-root' => {
		'loc' => 'c-root',
	    },
	    'd-root' => {
		'loc' => 'd-root',
	    },
	    'e-root' => {
		'loc' => 'e-root',
	    },
	    'f-root' => {
		'loc' => 'f-root',
	    },
	    'h-root' => {
		'loc' => 'h-root',
	    },
	    'i-root' => {
		'loc' => 'i-root',
	    },
	    'j-root' => {
		'loc' => 'j-root',
	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	    'l-root' => {
		'loc' => 'l-root',
	    },
	    'm-root' => {
		'loc' => 'm-root',
	    },
	},
	2012 => {
	    'a-root' => {
		'loc' => 'a-root',
	    },
	    'c-root' => {
		'loc' => 'c-root',
	    },
	    'e-root' => {
		'loc' => 'e-root',
	    },
	    'f-root' => {
		'loc' => 'f-root',
	    },
	    'h-root' => {
		'loc' => 'h-root',
	    },
	    'i-root' => {
		'loc' => 'i-root',
	    },
	    'j-root' => {
		'loc' => 'j-root',
	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	    'l-root' => {
		'loc' => 'l-root',
	    },
	    'm-root' => {
		'loc' => 'm-root',
	    },
	},
	2011 => {
	    'a-root' => {
		'loc' => 'a-root',
	    },
	    'c-root' => {
		'loc' => 'c-root',
	    },
	    'd-root' => {
		'loc' => 'd-root',
	    },
	    'e-root' => {
		'loc' => 'e-root',
	    },
	    'f-root' => {
		'loc' => 'f-root',
	    },
	    'h-root' => {
		'loc' => 'h-root',
	    },
	    'i-root' => {
		'loc' => 'i-root',
	    },
	    'j-root' => {
		'loc' => 'j-root',
	    },
	    'k-root' => {
		'loc' => 'k-root',
	    },
	    'l-root' => {
		'loc' => 'l-root',
	    },
	    'm-root' => {
		'loc' => 'm-root',
	    },
	},
	2010 => {
	    'a-root' => {
		'loc' => 'a-root',
	    },
	    'b-root' => {
		'loc' => 'b-root',
	    },
	    'c-root' => {
		'loc' => 'c-root',
	    },
	    'd-root' => {
		'loc' => 'd-root',
	    },
	    'e-root' => {
		'loc' => 'e-root',
	    },
	    'f-root' => {
		'loc' => 'f-root',
	    },
	    'g-root' => {
		'loc' => 'g-root',
	    },
	    'h-root' => {
		'loc' => 'h-root',
	    },
	    'i-root' => {
		'loc' => 'i-root',
	    },
	    'j-root' => {
		'loc' => 'j-root',
	    },
	    'k-root' => {
		'loc' => 'k-root',
	    },
	    'l-root' => {
		'loc' => 'l-root',
	    },
	    'm-root' => {
		'loc' => [ 'm-root', 'wide' ],
	    },
	},
	2009 => {
	    'a-root' => {
		'loc' => 'a-root',
	    },
	    'c-root' => {
		'loc' => 'c-root',
	    },
	    'e-root' => {
		'loc' => 'e-root',
	    },
	    'f-root' => {
		'loc' => 'f-root',
	    },
	    'h-root' => {
		'loc' => 'h-root',
	    },
	    'k-root' => {
		'loc' => 'k-root',
	    },
	    'l-root' => {
		'loc' => 'l-root',
	    },
	    'm-root' => {
		'loc' => 'm-root',
	    },
	},
	'2009_raw' => {
	    'a-root' => {
		'loc' => 'verisign',
	    },
	    'c-root' => {
		'loc' => 'cogent',
	    },
	    'e-root' => {
		'loc' => 'nasa',
	    },
	    'f-root' => {
		'loc' => 'isc',
	    },
	    'h-root' => {
		'loc' => 'arl',
	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	    'l-root' => {
		'loc' => 'icann',
	    },
	    'm-root' => {
		'loc' => 'wide',
	    },
	},
	2008 => {
	    'a-root' => {
		'loc' => 'verisign',
	    },
	    'c-root' => {
		'loc' => 'cogent',
	    },
	    'e-root' => {
		'loc' => 'nasa',
	    },
	    'f-root' => {
		'loc' => 'isc',
	    },
	    'h-root' => {
		'loc' => 'arl',
	    },
#	    'j-root' => {
#		'loc' => 'j-root',
#	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	    'l-root' => {
		'loc' => 'icann',
	    },
	    'm-root' => {
		'loc' => 'wide',
	    },
	},
	2007 => {
	    'c-root' => {
		'loc' => 'cogent',
	    },
	    'e-root' => {
		'loc' => 'nasa',
	    },
	    'f-root' => {
		'loc' => 'isc',
	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	    'm-root' => {
		'loc' => 'wide',
	    },
	},
	2006 => {
	    'c-root' => {
		'loc' => 'cogent',
	    },
	    'e-root' => {
		'loc' => 'nasa',
	    },
	    'f-root' => {
		'loc' => 'isc',
	    },
	    'k-root' => {
		'loc' => 'ripe',
	    },
	},
	);
}

###############################################################################
