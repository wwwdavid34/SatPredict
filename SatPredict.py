#!/eog/reference/anaconda3/bin/python

##===================================================================================
#
# SatPredict.py
#
# This code is designed to calculate the overpass time of satellite given
# an observer on the ground (Altitude = 0).
# This program is by default designed for NPP VIIRS, but can be used for other
# satellties with minimal modification needed. It is now utilizing TLE DB API hosted
# at boat.colorado.edu for weather and NOAA satellites. User can input their own
# TLE for predicting satellites not included in the TLE DB.
# 
# How to run:
#    Users need to create an instance, input parameters by changing the 
#    instance attributes. The run method will trigger the prediction process,
#    returning predicted result in nested dictionary.
# 
# Example:
#
#    == In Python Environment ==
#    import SatPredict
#    prd = SatPredict.SatPredict()
#    prd.tleL1='1 37849U 11061A   15010.14957891  .00000088  00000-0  62074-4 0  9888'
#    prd.tleL2='2 37849  98.6834 312.3948 0001412 123.3398 352.2834 14.19582225165950'
#    prd.startDate='2014-10-31'
#    prd.obsPos['lat']=-5.04309
#    prd.obsPos['lon']=136.9833
#    prd.obsPos['lat']=0
#    output = prd.run()
#
#    == At system prompt ==
#    SatPredict.py '2014-10-31' --output [path] --lat -5.04309 --lon 136.9833 --tle1 [tle1] --tle2 [tle2]
#
# Input:
#
#    ++++ TLE assigning ++++
#    .tleL1Input  User input TLE line one.
#    .tleL2Input  User input TLE line two.
#    .noradid     NORAD ID of the satelltie
#                 - SUOMI NPP: 37849
#                 - NOAA 20  : 43013
#
#    ++++ Time assigning ++++
#    .startDate   Prediction start date in format 'yyyy-mm'dd'
#    .predictDays Number of days to predict, default=3.
#    .start_jt  Prediction start time in julian day. NOTE: Input of .start_jt
#                      will prevail .startDate for it is a more precise way of designation.
#    .timeZone    Desired time zone for local time reporting in integers.
#    .useTLEEpoch Use the starttime of TLE instead of user input date/time.
#    
#    ++++ Spatial assigning ++++
#    .obsPos      Observer coordinates in decimat lat(deg)/lon(deg)/alt(m).
#                 NOTE: The input should be in dictionary format as 
#                 {'lat':x.xxx,'lon':x.xxx,'alt':0} Altitude should always be zero.
#    .swath       Satellite sensor swath. Default is 3000 Km for VIIRS.
#
#    ++++ Misc. input ++++
#    .verbose    Print prediction result and messages on screen.
#    .sphericalEarth   Assume Earth as a perfect sphere when calculating distance between 
#                      two locations on the surface. If turned off by set to False, 
#                      Vincenty's formulae will be used to give a more precise result.
#    .applyCorrection  Spherical assumption in distance calculation will induce latitudal
#                      errors in overpass time prediction. Such is corrected by applying
#                      a polynomial derived from 40K points of prediction around globe.
#                      By default is turned on, will be diabled if .spericalEarth is set
#                      to False.
# Output:
#      
#   Output is in nested dictionary foramt.
#   {'1':                                        < Numerical id of nexted dictionary
#        { 'id':x,                               < Numerical id of overpass
#          'satLat':x.xx,                        < Predicted satellite latitude
#          'satLon':x.xx,                        < Predicted satellite longitude
#          'scanAngle':x.xx,                     < Predicted scanangle from satellite
#          'distance':x.xx,                      < Predicted distance between 
#                                                  satellite and observer
#          'bearing':x.xx,                       < Predicted bearing angle (deg) from
#                                                  satellite to observer
#          'timeEndUTC':yyyy-mm-dd hh:mm:ss,     < UTC time of overpass in string format
#          'timeEndLOC':yyyy-mm-dd hh:mm:ss(z),  < Local time of overpass in string format
#          'timeEndUTC_J':x.xxx                  < UTC time of overpass in Julian
#          'timeEndLOC_J':x.xxx                  < Local time of overpass in Julina
#          'timeIniUTC_J':x.xxx                  < UTC initial time of prediction in Julian
#          'dayNight':x                          < 1:Daypass, 0:Nightpass
#   }}
#
# Dependency:
#   sgp4
#   jdcal
#
# Version History:
#   2015/6 v1.0
#   2015/7 v1.1 Enabled online TLE update for NPP.
#   2017/5 --   Modified TLE search algorithm to allow picking the latest TLE for future date.
#   2019/2 V2.0 Add database API for TLE querying
#               Cleaned the code for more reasonable variable passing
#               Upgraded syntax to Python3
#               Add calling method at system prompt
#
# Author:
#   David, Hsu
#   feng.c.hsu@noaa.gov
#   2015/6
#
##=======================================================================================


import os
import sys
import inspect
import glob
import math
from sgp4 import propagation
from sgp4 import io
from sgp4.earth_gravity import wgs72, wgs84
from datetime import datetime, timedelta
from sgp4.ext import days2mdhms, jday, invjday
from sgp4.propagation import sgp4
import jdcal
import time
import urllib
import re
import requests
import argparse

# Default settings

#tleAPI = 'http://boat.colorado.edu:3000/rpc/_a_ask_tle_norad'
tleAPI = 'http://eogdev.mines.edu:3000/rpc/_a_ask_tle_norad'
tleAPI2 = 'http://sharkube.com:3000/rpc/_a_ask_tle_norad'  # backup API
noradID = 37849  # default for SUOMI NPP
#tleList = []
#epoList = []
overpass = []
obsPos = {'lat': 0, 'lon': 0, 'alt': 0} # in decimal degrees
startDate = None  # format yyyy-mm-dd in UTC
predictDays = 3
verbose = True
applyCorrection = False  # By default will activate if spherical Earth is assumed
sphericalEarth = True  # False
tleL1 = None
tleL2 = None
tleL1Input = None
tleL2Input = None
start_jt = None
start_dt = None
satrec = None  # parsed TLE orbital elements

# Constants
mpd = float(24*60)
spd = float(24*60*60)
pi = math.pi
twopi = 2*pi
deg2rad = pi/float(180)
rad2deg = 1/deg2rad
earthR = 6378.137

# Setting
swath = float(3000)  # km
iteLimitDef = 1000
tspanDef = float(120)  # sec
timeZone = 0
useTLEEpoch = 0


class SatPredict(object):

    def __init__(self):
        # take assignments
        self.obsPos = obsPos
        self.tleAPI = tleAPI
        self.tleAPI2 = tleAPI2
        self.noradID = noradID
        self.startDate = startDate
        self.predictDays = predictDays
        self.sphericalEarth = sphericalEarth
        self.tleL1 = tleL1
        self.tleL2 = tleL2
        self.tleL1Input = tleL1Input
        self.tleL2Input = tleL2Input
        self.satrec = satrec
        self.verbose = verbose
        self.applyCorrection = applyCorrection
        self.start_jt = start_jt
        self.start_dt = start_dt
        self.timeZone = timeZone
        self.swath = swath
        self.useTLEEpoch = useTLEEpoch

    def run(self):
        # consolidate and check input variables
        self.check_time_tle()
        if self.satrec is None:
            sys.exit(1)
        result = self._run_predict(self.satrec, self.start_jt,
                                   self.obsPos, self.predictDays, self.verbose)
        return result

    def check_time_tle(self):
        # first, check input time or date
        # user input start julian time always prevail date,
        # no matter if date is also user input
        time_set = 1
        if self.start_jt is not None:
            self.start_dt = self.jd2date(self.start_jt)
            self.startDate = datetime.strftime(self.start_dt, '%Y-%m-%d')
        elif self.startDate is not None:
            self.start_dt = datetime.strptime(self.startDate, '%Y-%m-%d')
            self.start_jt = self.date2jd(self.start_dt)
        else:
            print('Warning: time/date not set.')
            time_set = 0

        # second, check if TLE L1/L2 is assigned
        # search for TLE and parse for L1/L2 if not assigned yet
        if self.tleL1Input is None or self.tleL2Input is None:
            if time_set == 1:
                self.satrec = self.get_satrec(self.startDate, self.noradID)
            else:
                print('Both time/date and TLE is not set!')
                sys.exit(1)

        # third, check if told to use TLE epoch
        # overwrite existing time/date or assign if there is none.
        if self.useTLEEpoch:
            print('use TLE epoch time.')
            self.start_jt = self.satrec.epoch
            self.start_dt = self.date2jd(self.start_jt)
            self.startDate = datetime.strftime(self.start_dt, '%Y-%m-%d')

    def date2jd(self, date):
        # convert datetime object to julian day
        return jday(date.year, date.month, date.day, date.hour, date.minute, date.second)

    def jd2date(self, jd):
        # convert julian day to datetime object
        d = invjday(jd)
        sec = int(d[5])
        msec = int(d[5] % 1 * 1000000)
        return datetime(d[0], d[1], d[2], d[3], d[4], sec, msec)

    def get_satrec(self, date, norad_id):

        r = self.ask_tle(date, norad_id, server=self.tleAPI)
        if r is None:
            r = self.ask_tle(date, norad_id, server=self.tleAPI2)
            if r is None:
                print('ERROR: No server available.')
                sys.exit(1)
        self.tleL1 = r[0]
        self.tleL2 = r[1]
        print(self.tleL1)
        print(self.tleL2)
        return io.twoline2rv(self.tleL1, self.tleL2, wgs72)

    def ask_tle(self, date, norad_id, server=None):

        if server is None:
            server = self.tleAPI

        if isinstance(date, type(datetime.today())):
            date = datetime.strftime(date, '%Y-%m-%d')

        r = requests.post(server, json={'input_epoch': date,
                                        'input_norad_id': norad_id})
        if r.raise_for_status() is None:
            print('TLE retrieve OK.')
            result = r.json()[0]
            tle_1 = result[u'line_1']
            tle_2 = result[u'line_2']
            diff = result[u'abs_diff']
            if ' ' in diff:
                days = int(diff.split(' ')[0])
            else:
                days = 0
            subs = diff.split(' ')[-1].split(':')
            hour = int(subs[0])
            mins = int(subs[1])
            secs = float(subs[2])
            diff = timedelta(days=days, hours=hour, minutes=mins, seconds=secs)
            self.tleL1 = tle_1
            self.tleL2 = tle_2
            if diff > timedelta(days=30):
                print('WARNING: TLE older than 30 days.')
            return [tle_1, tle_2, diff]

        else:
            print(r.text)
            return None

    def _run_predict(self,satrec, start_time, obsPos, predictDays, verbose, tleEpoch=False):

        # call predict method and run for designated time_rnage
        dtime = timedelta(days=0)
        pdays = timedelta(days=predictDays)
        ddtle = timedelta(days=0)

        cnt = 0
        
        # startTime=self.date2jd(startDate)
        dataLineBuff = ''

        if self.verbose:
            # Correction will only be applied when spherical earth assumption is true.
            if self.applyCorrection and self.sphericalEarth:
                print('============================================')
                print('NOTICE: PREDICTION TIME CORRECTION IS [[ON]]')
                print('============================================')

        while dtime < pdays:
            cnt += 1

            # update satrec if neccessary
            if (ddtle > timedelta(days=5) or ddtle < timedelta(days=-2)) or \
                    self.tleL1Input is not None:
                print(ddtle)
                self.satrec = self.get_satrec(self.jd2date(start_time), self.noradID)

            out = self.predict(self.satrec, start_time, obsPos)
            
            if cnt == 1:
                time_ini_utc = out['timeIniUTC']
 
            start_time = out['timeEndUTC'] + 900 / 86400.

            if out['error']:
                cnt -= 1
                continue
            eu = self.jd2date(out['timeEndUTC'])
            el = self.jd2date(out['timeEndLOC'])

            eu_str = datetime.strftime(eu, '%Y-%m-%d %H:%M:%S')
            el_str = datetime.strftime(el, '%Y-%m-%d %H:%M:%S') + \
                ''.join(['(', str(self.timeZone), ')'])

            data_line = [cnt, out['satLat'], out['satLon'], out['scanAngle'],
                         out['distance'], out['bearing'],
                         eu_str, el_str,
                         1 if (out['satVelZ'] >0) else 0]

            if self.verbose:
                print(data_line)

            # prepare output tuple of dictionaries
            a = {'id': cnt, 'satLat': out['satLat'], 'satLon': out['satLon'],
                 'scanAngle': out['scanAngle'], 'distance': out['distance'], 'bearing': out['bearing'],
                 'timeEndUTC': eu_str, 'timeEndLOC': el_str,
                 'timeEndUTC_J': out['timeEndUTC'], 'timeEndLOC_J': out['timeEndLOC'],
                 'timeIniUTC_J': out['timeIniUTC'],
                 'dayNight': data_line[-1]}
            if cnt == 1:
                result = {str(cnt): a}
            else:
                result[str(cnt)] = a

            # Take record of departed time from start, to know when to stop
            dtime = self.jd2date(out['timeEndUTC']) - self.jd2date(time_ini_utc)
            #print(self.satrec.epoch)
            ddtle = self.jd2date(out['timeEndUTC']) - self.satrec.epoch

        # return result in tuple of dictionaries
        return result
                
    # no iteration, direct propogation of satPos
    def propogate(self, satrec, startJTime, obsPos):
        obsGeo = {'x': obsPos['lon'], 'y': obsPos['lat'], 'z': obsPos['alt']}
        obsEci = {'x': 0, 'y': 0, 'z': 0}
        satGeo = {'x': 0, 'y': 0, 'z': 0}
        satEci = {'x': 0, 'y': 0, 'z': 0}

        actualEpoch = startJTime
        # surfaceDistance = 0
        # bearing = 0

        dtMinutes = (actualEpoch - satrec.jdsatepoch) * mpd
        r, v = sgp4(satrec, dtMinutes)

        satEci = {'x': r[0], 'y': r[1], 'z': r[2]}
        satVel = {'x': v[0], 'y': v[1], 'z': v[2]}

        satGeo = self._eci2geo(satEci, actualEpoch)
        obsEci = self._geo2eci(obsGeo, actualEpoch)
        scn = self._getVec(obsEci, satEci)  # scan direction vector from sat to obs
        satz = self._getAng(self._getVec(satEci, obsEci), obsEci) * rad2deg
        sata = self._getAsimuthEllipsoid(obsGeo, satGeo) * rad2deg

        bearing = self._getAng(scn, satVel) * rad2deg

        dx = satEci['x'] - obsEci['x']
        dy = satEci['y'] - obsEci['y']
        dz = satEci['z'] - obsEci['z']
        slant = math.sqrt(dx * dx + dy * dy + dz * dz)
        alpha = self._getAng(obsEci, satEci)
        scanAngle = math.asin(earthR * math.sin(alpha) / slant) * rad2deg

        # Spherical Earth big circle distance
        if self.sphericalEarth:
            ang = self._getAng(obsEci, satEci)
            surfaceDistance = (ang * earthR)
            try:
                surfaceDistance_v = self.getDis(obsGeo, satGeo)
            except:
                surfaceDistance_v = 0

        else:
            # Vincenty's Formulae
            try:
                surfaceDistance = self.getDis(obsGeo, satGeo)
            except:
                if self.verbose:
                    print('Vincenty\'s formulae failed. Fall back to spherical Earth.')
                ang = self._getAng(obsEci, satEci)
                if self.verbose:
                    print('Angle between coordinated: ' + '%.3f' % ang)
                surfaceDistance = (ang * earthR)

        return {'satLat': satGeo['y'], 'satLon': satGeo['x'], 'satAlt': satGeo['z'],
                'obsLat': obsGeo['y'], 'obsLon': obsGeo['x'], 'obsAlt': obsGeo['z'],
                'satVelX': satVel['x'], 'satVelY': satVel['y'], 'satVelZ': satVel['z'],
                'satEciX': satEci['x'], 'satEciY': satEci['y'], 'satEciZ': satEci['z'],
                'obsEciX': obsEci['x'], 'obsEciY': obsEci['y'], 'obsEciZ': obsEci['z'],
                'scanAngle': scanAngle,
                'distance': surfaceDistance,
                'bearing': bearing,
                'satz': satz, 'sata': sata
                }

    #make real propagator method and let it to be called from outside
    def predict(self, satrec, startJTime, obsPos):
        obsGeo={'x':obsPos['lon'],'y':obsPos['lat'],'z':obsPos['alt']}
        obsEci={'x':0,'y':0,'z':0}
        satGeo={'x':0,'y':0,'z':0}
        satEci={'x':0,'y':0,'z':0}

        bearingPrev     = 0 #initialize bearing buffer
        bearingDiffPrev = 100 #initialize bearing difference buffer
        beginnerFlag    = 2 #ignore the first 2 iterations for propagation init.
        propCnt         = 0 #initialize propagation count
        error           = 0 #error flag
        iteLimit        = iteLimitDef #propagation itemration limit
        halfSwath       = swath/2
        startEpoch      = startJTime

        actualEpoch     = startJTime
        surfaceDistance = 0
        bearing         = 0
        tspan           = tspanDef

        tspanBuff       = 0
        passedObsBuff   = 0
        visibleBuff     = 0
        passedObs       = 0
        visible         = 0

        #Start Propogation
        bearingPrecision=0.0001

        while (not(passedObs and visible and (math.fabs(bearingDiffPrev) < bearingPrecision)) 
               and not error):
            
            propCnt=propCnt+1

            if propCnt > iteLimit-1:
                if self.verbose:
                    print('Exceed iteration limit.')
                error=1

            dtMinutes=(actualEpoch - satrec.jdsatepoch)*mpd
            r,v=sgp4(satrec,dtMinutes)

            satEci={'x':r[0],'y':r[1],'z':r[2]}
            satVel={'x':v[0],'y':v[1],'z':v[2]}

            epoch=actualEpoch

            satGeo=self._eci2geo(satEci, actualEpoch)
            obsEci=self._geo2eci(obsGeo, actualEpoch)
            scn=self._getVec(obsEci,satEci) #scan direction vector from sat to obs
            satz = self._getAng(self._getVec(satEci, obsEci), obsEci) * rad2deg
            sata = self._getAsimuthEllipsoid(obsGeo, satGeo) * rad2deg

            bearingRaw=self._getAng(scn,satVel)*rad2deg

            bearing=bearingRaw
            if satGeo['x'] > obsGeo['x']: 
                bearing=0-bearingRaw

            bearingDiff=math.fabs(bearing)-90

            #check if propogation had passed the observer
            passedObs=0
            if (bearingDiff*bearingDiffPrev < 0) and not beginnerFlag:
                passedObs=1

            #decrease beginner flag count till zero
            beginnerFlag=beginnerFlag-1
            beginnerFlag=math.fabs(beginnerFlag*(beginnerFlag>0))

            #update bearing buffers
            bearingDiffPrev=bearingDiff
            bearingPrev=bearing

            #Spherical Earth big circle distance
            if self.sphericalEarth:
                ang=self._getAng(obsEci,satEci)
                surfaceDistance=(ang*earthR)
                try:
                    surfaceDistance_v=self.getDis(obsGeo,satGeo)
                except:
                    surfaceDistance_v=0

            else:
            #Vincenty's Formulae
                try:
                    surfaceDistance=self.getDis(obsGeo,satGeo)
                except:
                    if self.verbose:
                        print('Vincenty\'s formulae failed. Fall back to spherical Earth.')
                    ang=self._getAng(obsEci,satEci)
                    if self.verbose:
                        print('Angle between coordinated: '+'%.3f'%ang)
                    surfaceDistance=(ang*earthR)
                
            visible=0
            if (surfaceDistance < halfSwath):
                visible=1

            actualEpoch=actualEpoch+tspan/spd

            if (not passedObsBuff and passedObs) and (visibleBuff and not visible):
                visible=1

            #update buffer
            passedObsBuff = passedObs
            visibleBuff   = visible

            if (passedObs and visible):
                tspan=float(tspan)/(-20.)

        dx=satEci['x']-obsEci['x']
        dy=satEci['y']-obsEci['y']
        dz=satEci['z']-obsEci['z']
        slant=math.sqrt(dx*dx+dy*dy+dz*dz)
        alpha=self._getAng(obsEci,satEci)
        scanAngle=math.asin(earthR*math.sin(alpha)/slant)*rad2deg

        #Correction will only be applied when spherical earth assumption is true.
        if self.applyCorrection and self.sphericalEarth:
            endTimeJulUtc=self._applyCorrection(actualEpoch,obsGeo['y'])
        else:
            endTimeJulUtc=actualEpoch

        endTimeJulLoc=endTimeJulUtc+(self.timeZone)/24.
        iniTimeJulLoc=startEpoch+(self.timeZone)/24.

        return {'satLat':satGeo['y'],'satLon':satGeo['x'],'satAlt':satGeo['z'],
                'obsLat':obsGeo['y'],'obsLon':obsGeo['x'],'obsAlt':obsGeo['z'],
                'satVelX':satVel['x'],'satVelY':satVel['y'],'satVelZ':satVel['z'],
                'satEciX':satEci['x'],'satEciY':satEci['y'],'satEciZ':satEci['z'],
                'obsEciX':obsEci['x'],'obsEciY':obsEci['y'],'obsEciZ':obsEci['z'],
                'scanAngle':scanAngle,
                'distance':surfaceDistance,
                'bearing':bearing,
                'satz':satz, 'sata':sata,
                'timeEndUTC':endTimeJulUtc, 'timeIniUTC':startEpoch,
                'timeEndLOC':endTimeJulLoc, 'timeIniLOC':iniTimeJulLoc,
                'timeZone':timeZone,
                'propCnt':propCnt, 'timeSpan':tspan,
                'error':error}

#==================
## TOOL CHEST
#==================

    def getGreatCircleAng(self,lla1,lla2):
        lat1 = lla1['y']*deg2rad
        lat2 = lla2['y']*deg2rad
        lon1 = lla1['x']*deg2rad
        lon2 = lla2['x']*deg2rad
        d = math.acos((math.sin(lat1)*math.sin(lat2))+(math.cos(lat1)*math.cos(lat2)*math.cos(abs(lon1-lon2))))
        return d

    def _applyCorrection(self, t, lat):
        #apply correction for sphere assumption in propogation
        # input t in Julian                                
        # Y=7E-8*X^4+2E-5*X^3-3E-4*X^2-9.61E-2*X-0.7046 R2=0.885
        # Y: Departed seconds, X: Latitude of observer
        if lat < 65 and lat > -80:
            cor=7e-8*lat**4+2e-5*lat**3-3e-4*lat**2-9.61*lat-0.7046
        else:
            cor=0
        return t-cor/spd

    def _getAsimuthEllipsoid(self, p1, p2):
        # Wikipedia Azimuth
        phi1 = p1['y']*deg2rad
        phi2 = p2['y']*deg2rad
        L1   = p1['x']*deg2rad
        L2   = p2['x']*deg2rad
        f    = 1/298.257223563
        L    = L2 - L1
        e2   = f * (2-f)
        oneme2 = (1-f) * (1-f)
        A1   = oneme2*math.tan(phi2)/math.tan(phi1)
        A2 = e2 * math.sqrt(
            (1 + oneme2 * (math.tan(phi2) * math.tan(phi2))) / (1 + oneme2 * (math.tan(phi1) * math.tan(phi1))))
        A = A1 + A2
        if phi1 == 0:
            alpha = math.atan(math.sin(L) / oneme2 / math.tan(phi2))
        else:
            alpha = math.atan(math.sin(L) / (A-math.cos(L)) / math.sin(phi1))
        if p2['y'] < p1['y']:
            # 2nd and 3rd quadrant
            if p2['x'] > p1['x']:
                # 2nd
                sata=alpha+math.pi
        
            else:
                # 3rd
                sata=alpha-math.pi
        else:
            if p2['x'] < p1['x']:
                # 4th quadrant
                sata=alpha
            else:
                # 1st quadrant
                sata=alpha

        return sata

    def _getAng(self, v1,v2):
        #return angle between vevtors in rad
        ang = math.acos((v1['x']*v2['x']+v1['y']*v2['y']+v1['z']*v2['z'])/
                        (math.sqrt(v1['x']**2+v1['y']**2+v1['z']**2)*
                         math.sqrt(v2['x']**2+v2['y']**2+v2['z']**2)))

        return ang

    def _getVec(self, p1,p2):
        v={'x':p1['x']-p2['x'],
           'y':p1['y']-p2['y'],
           'z':p1['z']-p2['z']}
        n=math.sqrt(v['x']*v['x']+v['y']*v['y']+v['z']*v['z'])
        return {'x':v['x']/n,
                'y':v['y']/n,
                'z':v['z']/n}
    '''
    Taken from sgp4.propagation._gstime(jdut1)
    '''
    def _gstime(self, jdut1):
        tut1 = (jdut1 - 2451545.0) / 36525.0
        temp = (-6.2e-6* tut1 * tut1 * tut1 + 0.093104 * tut1 * tut1 + 
                 (876600.0*3600 + 8640184.812866) * tut1 + 67310.54841)  #  sec                                         
        temp = (temp * deg2rad / 240.0) % twopi # 360/86400 = 1/240, to deg, to rad                                    

     #  ------------------------ check quadrants ---------------------                                              
        if temp < 0.0:
            temp += twopi

        return temp

    def _geo2eci(self, geo_pos,jd):
        gmst=self._gstime(jd)
        geoPosT={'longitude':geo_pos['x']*deg2rad,
                 'latitude':geo_pos['y']*deg2rad,
                 'height':geo_pos['z']}
        ecfPos =self._geo2ecf(geoPosT)#,gmst)
        eciPos =self._ecf2eci(ecfPos,gmst)
        return eciPos

    def _geo2ecf(self,geodetic_coords):
        longitude=geodetic_coords['longitude']
        latitude=geodetic_coords['latitude']
        height=geodetic_coords['height']
        a=6378.137
        b=6356.7523142
        f=(a-b)/a
        e2=((2*f)-(f*f))
        normal=a/math.sqrt(1-(e2*(math.sin(latitude)*math.sin(latitude))))
        
        return {'x': (normal+height)*math.cos(latitude)*math.cos(longitude),
                'y': (normal+height)*math.cos(latitude)*math.sin(longitude),
                'z': ((normal*(1-e2))+height)*math.sin(latitude)}

    def _ecf2eci(self,ecf_coords,gmst):
        # ccar.colorado.edu/ASEN5070/handouts/coordsys.doc
        #
        #[X]    [C -S  0][X]
        #[Y]  = [S  C  0][Y]
        #[Z]eci [0  0  1][Z]ecf
        #
        return {'x': (ecf_coords['x']*math.cos(gmst))-(ecf_coords['y']*math.sin(gmst)),
                'y': (ecf_coords['x']*(math.sin(gmst)))+(ecf_coords['y']*math.cos(gmst)),
                'z': ecf_coords['z']}

    def _eci2geo_secondary(self,eci_coords,jd):
        #Taken from IDL code eci_to_lla.pro

        # f = Earth oblateness flatteing factor
        f=1./298.257
        re=earthR

        # Get Greenwich sidereal time
        gmst = self._gstime(jd)

        #Calculate length of position vector
        rs = math.sqrt(eci_coords['x']**2+eci_coords['y']**2+eci_coords['z']**2)
        
        # Calculate normalized position vector
        rnx = eci_coords['x']/rs
        rny = eci_coords['y']/rs
        rnz = eci_coords['z']/rs

        #Calculate declination, geodetic latitude and altitude above oblate sphere
        dec = math.asin(rnz)
        lat = math.atan(math.tan(dec)/(1.-f)**2)
        alt = re * (rs/re-(1-f)/(math.sqrt(1-f*(2-f)*(math.cos(dec))**2)))

        #Calculate right ascension and geocentric longitude of satellite
        ra = math.atan2(rny,rnx)
        lon=math.atan2(math.sin(ra-gmst),math.cos(ra-gmst))
        
        #Convert radians into degrees
        lla=eci_coords
        lla['x']=lon*rad2deg
        lla['y']=lat*rad2deg
        lla['z']=alt

        return lla

    def _eci2geo(self,eci_coords, jd):

        # Credit
        #/*
        #* satellite-js v1.1
        #* (c) 2013 Shashwat Kandadai and UCSC
        #* https://github.com/shashwatak/satellite-js
        #* License: MIT
        #*/

        #use strict';
        #// http://www.celestrak.com/columns/v02n03/

        gmst=self._gstime(jd)
        
        a=6378.137
        b=6356.7523142
        R  = math.sqrt((eci_coords['x']*eci_coords['x'])+(eci_coords['y']*eci_coords['y']))
        f  = (a-b)/a
        e2 = ((2*f)-(f*f))
        longitude = math.atan2(eci_coords['y'],eci_coords['x'])-gmst

        kmax = 20
        k = 0
        latitude = math.atan2(eci_coords['z'],
                              math.sqrt(eci_coords['x']*eci_coords['x']+
                                        eci_coords['y']*eci_coords['y']))
        
        C=0
        while (k<kmax):
            C=1/math.sqrt(1-e2*(math.sin(latitude)*math.sin(latitude)))
            latitude=math.atan2(eci_coords['z']+(a*C*e2*math.sin(latitude)),R)
            k+=1
        height=(R/math.cos(latitude))-(a*C)

        longitude = longitude*rad2deg
        latitude = latitude*rad2deg

        #Warp longitude between -180 and 180 degrees
        if longitude < -180: longitude = longitude+360

        return {'x':longitude,'y':latitude,'z':height}

##=============
# Currently this precise distance calculation is not yet fully tested. And
# might prone to error. Legacy spherical model with prediction time correction
# should be used when running automate large volume task.
##=============


    def getDis(self, coord1, coord2):
        #calculate distance between two lat/lon coordinates
        # coord1, coord2: lat/lon in degree

        if coord1['x']==coord2['x'] and coord1['y']==coord2['y']:
            return 0.

        #convert coords to rad
        phi1=coord1['y']*deg2rad
        lembda1=coord1['x']*deg2rad
        phi2=coord2['y']*deg2rad
        lembda2=coord2['x']*deg2rad

        ##===================
        # Following code block taken from 
        # ftp://pdsimage2.wr.usgs.gov/pub/pigpen/Python/Geodetic_py.py
        # Courtesy to Jim Leven
        #====================
        """ 
        Returns the distance between two geographic points on the ellipsoid
        and the forward and reverse azimuths between these points.
        lats, longs and azimuths are in decimal degrees, distance in metres 

        Returns ( s, alpha12,  alpha21 ) as a tuple
        """

        if (abs( phi2 - phi1 ) < 1e-8) and ( abs( lembda2 - lembda1) < 1e-8 ) :
                return 0.0, 0.0, 0.0


        f=1.0 / 298.257223563 #WGS94
        a=earthR*1000 #meters
        b = a * (1.0 - f)

        TanU1 = (1-f) * math.tan( phi1 )
        TanU2 = (1-f) * math.tan( phi2 )

        U1 = math.atan(TanU1)
        U2 = math.atan(TanU2)

        lembda = lembda2 - lembda1
        last_lembda = -4000000.0 # an impossibe value
        omega = lembda

        # Iterate the following equations, 
        #  until there is no significant change in lembda 

        cnt=0
        while ( last_lembda < -3000000.0 or lembda != 0 and abs( (last_lembda - lembda)/lembda) > 1.0e-9 ) :
                cnt=cnt+1
#                if cnt > 10000: 
#                    print [last_lembda,lembda,abs( (last_lembda - lembda)/lembda),                                                                                        ( last_lembda < -3000000.0 or lembda != 0 and abs( (last_lembda - lembda)/lembda) > 1.0e-9 )] 
                sqr_sin_sigma = pow( math.cos(U2) * math.sin(lembda), 2) + \
                        pow( (math.cos(U1) * math.sin(U2) - \
                        math.sin(U1) *  math.cos(U2) * math.cos(lembda) ), 2 )

                Sin_sigma = math.sqrt( sqr_sin_sigma )

                Cos_sigma = math.sin(U1) * math.sin(U2) + math.cos(U1) * math.cos(U2) * math.cos(lembda)
        
                sigma = math.atan2( Sin_sigma, Cos_sigma )

                Sin_alpha = math.cos(U1) * math.cos(U2) * math.sin(lembda) / math.sin(sigma)
                alpha = math.asin( Sin_alpha )

                Cos2sigma_m = math.cos(sigma) - (2 * math.sin(U1) * math.sin(U2) / pow(math.cos(alpha), 2) )

                C = (f/16) * pow(math.cos(alpha), 2) * (4 + f * (4 - 3 * pow(math.cos(alpha), 2)))

                last_lembda = lembda

                lembda = omega + (1-C) * f * math.sin(alpha) * (sigma + C * math.sin(sigma) * \
                        (Cos2sigma_m + C * math.cos(sigma) * (-1 + 2 * pow(Cos2sigma_m, 2) )))

                if cnt > 100: raise os.error
        u2 = pow(math.cos(alpha),2) * (a*a-b*b) / (b*b)

        A = 1 + (u2/16384) * (4096 + u2 * (-768 + u2 * (320 - 175 * u2)))

        B = (u2/1024) * (256 + u2 * (-128+ u2 * (74 - 47 * u2)))

        delta_sigma = B * Sin_sigma * (Cos2sigma_m + (B/4) * \
                (Cos_sigma * (-1 + 2 * pow(Cos2sigma_m, 2) ) - \
                (B/6) * Cos2sigma_m * (-3 + 4 * sqr_sin_sigma) * \
                (-3 + 4 * pow(Cos2sigma_m,2 ) )))

        s = b * A * (sigma - delta_sigma)

##=========================================================
##Do not need this part for calculating forward/reverse azimuth
#        alpha12 = math.atan2( (math.cos(U2) * math.sin(lembda)), \
#                (math.cos(U1) * math.sin(U2) - math.sin(U1) * math.cos(U2) * math.cos(lembda)))

#        alpha21 = math.atan2( (math.cos(U1) * math.sin(lembda)), \
#                (-math.sin(U1) * math.cos(U2) + math.cos(U1) * math.sin(U2) * math.cos(lembda)))

#        if ( alpha12 < 0.0 ) : 
#                alpha12 =  alpha12 + two_pi
#        if ( alpha12 > two_pi ) : 
#                alpha12 = alpha12 - two_pi

#        alpha21 = alpha21 + two_pi / 2.0
#        if ( alpha21 < 0.0 ) : 
#                alpha21 = alpha21 + two_pi
#        if ( alpha21 > two_pi ) : 
#                alpha21 = alpha21 - two_pi

#        alpha12    = alpha12    * 45.0 / piD4
#        alpha21    = alpha21    * 45.0 / piD4last_lembda = -4000000.0lembda1 = lembda1 * piD4 / 45.0
##========================================================
        return s/1000 #convert to KM
        

# ========
# Prompt Execution
# ========

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Run satellite predictor.')
    parser.add_argument('date', metavar='yyyy-mm-dd (or Julian)', type=str, nargs=1,
                        help='Date to start prediction.')
    parser.add_argument('--julian', '-j', dest='julian', action='store_true',
                        help='Input time is in Julian date.')
    parser.add_argument('--latitude', '-lat', dest='lat',  nargs='?',
                        default=0.0, type=float,
                        help='Observer latitude (default 0)')
    parser.add_argument('--longitude', '-lon', dest='lon',  nargs='?',
                        default=0.0, type=float,
                        help='Observer longitude (default 0)')
    parser.add_argument('--swath', '-s', dest='swath', nargs='?',
                        default=3000, type=float,
                        help='Sensor swath in KM.')
    parser.add_argument('--ndays', '-nd', dest='ndays',  nargs='?',
                        default=3, type=int,
                        help='Number of days to predict (default 3)')
    parser.add_argument('--norad_id', '-id', dest='norad_id',  nargs='?',
                        default=37849, type=int,
                        help='NORAD ID of the satellite (default 37849 for SUOMI NPP')
    parser.add_argument('--output', '-o', dest='output', nargs='?',
                        default='', type=str,
                        help='Path to the output CSV.')
    parser.add_argument('--header', '-d', dest='header', action='store_true',
                        help='Add header to output CSV.')
    parser.add_argument('--timezone', '-tz', dest='timezone', nargs='?',
                        default=0, type=int,
                        help='Set local time zone.')
    parser.add_argument('--verbose', '-v', dest='verbose', action='store_true',
                        help='Verbose output print.')

    args = parser.parse_args()

    prd = SatPredict()
    if args.date[0] == '':
        print('Must input date (yyyy-mm-dd).')
        sys.exit(1)
    date = args.date[0]
    if args.julian:
        date = prd.jd2date(float(args.date[0]))
        date = datetime.strftime(date, '%Y-%m-%d')
        print('Julian to date:',date)
    prd.startDate = date
    if args.lat != 0.0:
        prd.obsPos = {'lat': args.lat,
                      'lon': args.lon,
                      'alt': 0.0}
    prd.swath = args.swath
    prd.predictDays = args.ndays
    prd.noradID = args.norad_id
    prd.timeZone = args.timezone
    prd.verbose = args.verbose

    #print(args.header)
    out = prd.run()
    #print(out)
    if args.output != '':
        f = open(args.output, 'w')
        if args.header:
            first_line = out[list(out)[0]]
            header = list(first_line)
            f.write(','.join([str(i) for i in header])+'\n')
        seq = [int(i) for i in list(out)]
        seq.sort()
        seq = [str(i) for i in seq]
        for i in seq:
            data = [str(out[i][j]) for j in list(out[i])]
            #print(data)
            f.write(','.join(data)+'\n')


