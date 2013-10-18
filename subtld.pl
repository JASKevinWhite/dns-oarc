#!/usr/bin/perl

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
#use DBM::Deep;

$SIG{CHLD} = \&REAPER;

our $VERSION = '$Id: subtld.pl 57 2013-10-15 01:41:55Z kwhite $';

#use PerlIO::gzip;
#use threads;

# bytld entries aren't used.  They used to be, but they are calculated
# now, and assumed to be somewhere in the DSTBASE tree.  I have left
# the definitions in here as a note, in case their use needs to be
# resurrected.  Use case: one user wishes to use processed data in
# another user's directory.

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
	      'raw' => '/mnt/oarc-pool4/DITL-20100413/RAW',
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

my $DSTBASE = $ENV{HOME}.'/jas/gtld';

my $MAXPROC = 12;
my $MAXPROC_TCPDUMP = 40;
my $MAXPROC_SORT = 15;

# Data structures for global TLD/Interisle categorization
my %OLDGTLD;
my %NEWGTLD;
my %INSIP;
my %INXMP;

# Data structures to handle children
my %CHILDREN;
my @STIFFS;

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

sub CopyAndSub {
    my ($src, $dst_loc, $gtld, $year) = @_;
    my $dst = $dst_loc."/".$gtld.".gz";
    my $dst_log = $dst_loc."/".$gtld."_log.gz";
    my $dst_dbfilename = $dst_loc."/".$gtld.".db";
    my $dst_log_nocollapse = $dst_loc."/".$gtld."_lognocollapse.gz";
    my $dst_interisle_log = $dst_loc."/".$gtld."_interisle.gz";
    my $droplist;
    my %intsum;

#    print "$src\t$dst\t$gtld\t$year\n";

    my ($use_db, $db);
    if (($year == 2013) && ($gtld eq "home")) { $use_db = 1};
    if (($gtld eq "home") || ($gtld eq "corp")) { return();};

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
	my ($scrub, $interisle, $retrow, $qstr, $sld) = 
	    ScrubAndInterisle($_);
	if (!defined $scrub) { next; }
	addToDrop($droplist, $scrub, $qstr, $sld);
	$intsum{$interisle}++;
	print $out $retrow."\n";
    }
    close(IN);
    close($out);

    # Create two summary files.  $dst_log_nocollapse just has one row
    # per qstr, with a count, sorted by sld.  $dst_log is more
    # difficult.  Start with an SLD.  A row is present in this file if
    # there were any _valid_ queries to a name in that SLD.  If all of
    # the queries present were invalid, or random, the SLD is removed
    # from the list.

    open(my $outlog, "| gzip -c > $dst_log") || die "ERROR: failed to open output file $dst_log: $!";
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

    my $DOVALIDCHECKS = 0;
    
    chomp($src);
    my $interisle = "INNONE";
    my $scrub = "OK";
    my @elem = split(/ /, $src);
#2011-04-12 20:54:06.876091 gree blog a-root 119.63.192.232 198.41.0.4 blog.gree
    my $gtld = $elem[2];
    my $root = $elem[4];
    if ((!defined $root) || ($root eq "")) {
	# This only happened due to an earlier bug in the raw stage.
	# It shouldn't happen in future runs.
#	print "no root: $_\n";
	return(undef);
    }
    my $qstr = $elem[7];
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
    
    # If total string is too long
    # We want to count total characters in name.
    # $qstr can have extra ^ as escape characters.
    # ^^ means a single ^.  Replace it with $ to get it out of the
    # way.  Then remove all remaining ^ characters (since they're
    # just excape characters).
    my $qstrlen = $qstr;
    $qstrlen =~ s/\^\^/\$/g;
    $qstrlen =~ s/\^//g;
    if (length($qstrlen) > 253) {
	$scrub = "INVALID";
	$scrubbed++;
    }

    if (!$scrubbed && defined $sld) {
	if (length($sld) < 3) {
#	    print "SHORTSLD: $qstr\n";
	    $scrub = "SHORTSLD";
	    $scrubbed++;
	}
    }

    if ($DOVALIDCHECKS) {
    if (!$scrubbed && defined $sld) {
	# If sld has any invalid characters
	if ($sld =~ /[^a-zA-Z0-9\-]/) {
	    $scrub = "INVALID";
	    $scrubbed++;
	}
	elsif ((substr($sld, 2, 1) eq "-") &&
	       (substr($sld, 0, 2) ne "xn")) {
#	    print "INVALIDDASH $qstr\n";
	    $scrub = "INVALID";
	    $scrubbed++;
	}
	elsif (index($sld, '_') != -1) {
#	    print "INVALIDUNDERSCORE $qstr\n";
	    $scrub = "INVALID";
	    $scrubbed++;
	}
    }
    
    # Walk through the labels, look for any that start or end with a
    # dash.
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

    if ($DOVALIDCHECKS) {
    # Look for 10/13 character random
    if (!$scrubbed) {
	if ((length($flabel) == 10) && (!$OVERRIDE10{$flabel})) {
	    # If it only consists of a-z, we consider it "random" 
	    if ($flabel =~ /^[a-zA-Z]*$/) {
		$scrub = "RANDOM10";
		$scrubbed++;
	    }
	}
	elsif ((length($flabel) == 13) && (substr($flabel, 0, 4) ne "xn--") && (!$OVERRIDE13{$flabel})) {
	    # If it starts with a-z and contains a digit, we consider it "random"
	    # can contain dashes.  Mostly only see up to 2, but this regexp 
	    # allows any number.  Also, if it starts with "xn--", is isn't random.
	    # That check was needed when dashes were added.
	    if ($flabel =~ /^[a-z][a-z0-9\-]*[0-9][a-z0-9\-]*$/) {
		$scrub = "RANDOM13";
		$scrubbed++;
	    }
	}
    }
    }
    $elem[7] = $scrub;
    $elem[8] = $interisle;
    $elem[9] = $qstr;
    my $retrow = join(" ", @elem);

    return($scrub, $interisle, $retrow, $qstr, $sld);
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
    my (@src) = @_;
    
    # A source should exist and be a directory

    my $badcount;

    foreach my $src (@src) {
	if (!-d $src) {
	    print "Source $src is not a directory.\n";
	    $badcount++;
	}
    }
    if ($badcount) { exit(2); }
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
    my ($year, $suffix) = @_;

    my ($raw, $intermediate, $bytld, $jas);

    $raw = $LOC{$year}{raw};

    $intermediate = $DSTBASE."/intermediate/".$LOC{$year}{date}."-".$suffix;
    $bytld = $DSTBASE."/by-tld/".$LOC{$year}{date}."-".$suffix;
    $jas = $DSTBASE."/jas/".$LOC{$year}{date}."-".$suffix;

    return($raw, $intermediate, $bytld, $jas)
}

############################################################################### 

sub FindRawFiles {
    my ($year, $map, $src) = @_;
    
    my $rawFiles = [ ];

#    print Dumper($map);
    foreach my $root (sort(keys(%$map)))
    {
	my $cmd = "find \"$src/$map->{$root}{loc}\" -type f";
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
#	    print Dumper(\%file);
	}
    }
    return($rawFiles);
}

############################################################################### 

sub ParseRawFiles {
    my ($rawFiles, $dst, $bytld_dst) = @_;

    my $sleeptime = 0;
    my $qlen = scalar(@$rawFiles);
    
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
	    DumpPcap($file->{src}, $fulldest."/".$file->{dst}, $bytld_dst);
#	    print "ChildEnd: $file\n";
	    exit(0);
	}
	
	$qlen = scalar(@$rawFiles);
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

sub DumpPcap {
    my ($src, $dst, $bytld_dst) = @_;

    print "DumpPcap: $src $dst $bytld_dst\n";
#    return(1);

    open(my $outlog, "| gzip -c > $dst") || die "ERROR failed to open output file $dst: $!";
    open(IN, "gunzip -dc \"$src\" | tcpdump -tttt -n -s 0 -r - 2> /dev/null |") || die "ERROR failed to open input file and tcpdump $src: $!";
    my %files;

#    gunzip -dc "$infile" | tcpdump -n -s 0 -r - 2> /dev/null | ./filter-tcpdump-tldlist.pl $tldlist | gzip -6 > $outname.gz
#14:19:59.081577 IP6 2a02:2098:8711:8c21:0:2:b19:b00b.24372 > 2001:503:ba3e::2:30.53: 23630 [1au] A? www.hybridtraffic.com.home. (55)
#2013-05-29 14:19:59.081577 IP6 2a02:2098:8711:8c21:0:2:b19:b00b.24372 > 2001:503:ba3e::2:30.53: 23630 [1au] A? www.hybridtraffic.com.home. (55)

    while (<IN>) {
#	print "$_";
	# The query is at the end.  It ends with the final ".".  It
	# starts past the ? in the query type.  If you can't find a ?
	# followed by a space, then this isn't a valid query row.
	# Look for the first "? " string, because, in theory "? " is
	# actually a valid part of a domain name
	my $nameend = rindex($_, ".");
	my $namestart = index($_, "? ");
	next unless $namestart > -1;
	my $name = substr($_, $namestart+2, $nameend-$namestart-2);
	$name = lc($name);

        my $tldstart = rindex($name, ".");
        next if $tldstart == -1;
        my $tld = substr($name, $tldstart+1);
        next unless defined $NEWGTLD{$tld};
#	print "i care: :$tld:\n";

	# Replace all spaces with ^$ 
	# TCPDUMP uses various ^x for non-printable characters, and ^^
	# for the ^ itself.  It doesn't seem to output ^$ for
	# anything.
	# Note: TCPDUMP's output for characters > 127 is actually bad,
	# and darn near un-parseable.  Every octet has an M- in
	# front of it, which is indistinguishable from a REAL string
	# of "M-".  Which means I can't just go through and remove all
	# "M-" for count purposes.  So, basically, any name that comes
	# through with characters > 128 will have their length counted
	# wrong, and could get thrown out for being "too long", even
	# if they weren't.
	$name =~ y/ /^$/;

	my $typestart = rindex($_, " ", $namestart-1);
	# -1 removes the ? at the end
	my $type = substr($_, $typestart+1, $namestart-$typestart-1);
	my @parts = split(/ /, $_, 7);

	my $date = $parts[0];
	my $time = $parts[1];
        my $sip  = $parts[3];
        my $sipe = rindex($sip, ".");
        substr($sip, $sipe) = "";
        my $dip   = $parts[5];
        my $dipe = rindex($dip, ".");
        substr($dip, $dipe) = "";
	my $root = $ROOTBYIP{$dip};
	if (!defined $root) {
	    # The destination IP address doesn't match any known root
	    # address, so we're going to ignore this row.
	    print "non-root: $src $_";
	    next;
	}
        my @dom_parts = split(/\./, $name);
        pop @dom_parts;
        my $sld = pop @dom_parts || ".";

	print $outlog join " ", $date, $time, $sip, $dip, $root, $type, $name, "\n";
	my $file = $tld;
	if (!defined $files{$file}) {
            #$files{$file} = new IO::Compress::Gzip "$outdir/$file" || die "gzip failed: $GzipError";
            open(my $fh, ">>", "$bytld_dst/$file") || die "ERROR: failed to open for $tld: $!";
            $files{$file} = $fh;
        }
        my $fh = $files{$file};
        syswrite $fh, "$date $time $tld $sld $root $sip $dip $name\n";
    }
    close($outlog);
    close(IN);
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
    print "          --raw: do processing of RAW data\n";
    print "          --jas: do processing of JAS summarization\n";
    print "          (Without --raw or --jas, nothing will be done.)\n";
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

    my ($year, $suffix);

    GetOptions("single=s" => \$single,
	       'suffix=s' => \$suffix,
	       'year=i' => \$year,
	       'raw' => \$doRaw,
	       'jas' => \$doJAS,
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
    my ($raw, $intermediate, $bytld, $jas) = CalcSrcDst($year, $suffix);

    if ($doRaw)
    {
	VerifySrc($raw);
	VerifyDst($intermediate, $bytld);
	my $rawFiles = FindRawFiles($year, $ROOTMAP{$year}, $raw);
	ParseRawFiles($rawFiles, $intermediate, $bytld);
	SortByTld($bytld);
	CompressByTld($bytld);
    }
	
    if ($doJAS)
    {
	VerifySrc($bytld);
	VerifyDst($jas);
	if (defined $single) { 
	    my $file = $single;
	    if ($file =~ /^(.*).gz$/) {
		my $gtld = $1;
		CopyAndSub($bytld."/".$file,
			   $jas,
			   $gtld,
			   $year);
	    } 
	}
	else {
	    opendir(DIR, $bytld);
	    my @files = readdir(DIR);
	    closedir(DIR); 
	    my @files2;
	    foreach my $file (@files) {
		if ($file =~ /^(.*).gz$/) {
		    push(@files2, $file);
		}
	    }
	    runCopyAndSub(\@files2, $bytld, $jas, $year);
	}
    }
}
 
############################################################################### 

sub runCopyAndSub {
    my ($files, $src, $dst, $year) = @_;
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
	my $file = shift(@$files);
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
		'loc' => 'm-root',
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
