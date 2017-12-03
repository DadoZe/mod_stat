#!/usr/bin/python
import AccountCommands
import ArenaType
import BigWorld
import ResMgr
import codecs
import datetime
import json
import math
import os
import re
import threading
import urllib
import urllib2
from Account import Account
from Queue import Queue
from account_helpers import BattleResultsCache
from debug_utils import *
from gui import DialogsInterface
from gui import SystemMessages
from gui.Scaleform.daapi.view.dialogs import SimpleDialogMeta, I18nConfirmDialogButtons
from gui.shared.utils.requesters import StatsRequester
from helpers import i18n
from items import vehicles as vehiclesWG
from messenger import MessengerEntry
from messenger.formatters.service_channel import BattleResultsFormatter
from notification.NotificationListView import NotificationListView
from notification.NotificationPopUpViewer import NotificationPopUpViewer
from xml.dom.minidom import parseString

GENERAL = 0
BY_TANK = 1
VERSION = '0.9.20.1.4'
URLLINK = 'http://bit.ly/YasenKrasen'

print 'Loading mod: YasenKrasen Session Statistics ' + VERSION + ' (http://forum.worldoftanks.eu/index.php?/topic/583433-)'

def hexToRgb(hex):
    return [int(hex[i:i+2], 16) for i in range(1,6,2)]

def gradColor(startColor, endColor, val):
    start = hexToRgb(startColor)
    end = hexToRgb(endColor)
    grad = []
    for i in [0, 1, 2]:
        grad.append(start[i]*(1.0 - val) + end[i]*val)
    return '#%02x%02x%02x' % (grad[0], grad[1], grad[2])

class SessionStatistic(object):

    def __init__(self):
        self.page = GENERAL
        self.cacheVersion = 10
        self.queue = Queue()
        self.loaded = False
        self.configIsValid = True
        self.battleStats = {}
        self.cache = {}
        self.gradient = {}
        self.palette = {}
        self.config = {}
        self.expectedValues = {}
        self.values = {}
        self.battles = []
        self.battleStatPatterns = []
        self.messageGeneral = ''
        self.messageByTank = ''
        self.playerName = ''
        self.bgIcon = ''
        self.startDate = None
        self.battleResultsAvailable = threading.Event()
        self.battleResultsAvailable.clear()
        self.battleResultsBusy = threading.Lock()
        self.thread = threading.Thread(target=self.mainLoop)
        self.thread.setDaemon(True)
        self.thread.start()

    def load(self):
        if self.loaded and self.playerName == BigWorld.player().name:
            return
        self.loaded = True
        self.battles = []
        self.playerName = BigWorld.player().name
        path = '/'.join(['.', 'mods', 'configs', 'yk-stats'])
        if not os.path.exists(path):
            path = '/'.join(['.', 'res_mods', 'configs', 'yk-stats'])
        if os.path.isdir(path):
            self.configFilePath = '/'.join([path, 'config.json'])
            self.statCacheFilePath = '/'.join([path, 'cache.json'])
            self.expectedValuesPath = '/'.join([path, 'expected_tank_values.json'])
        self.readConfig()

        if self.config.get('updateExpectedTankValues', True):
            expurl = self.config.get('urlForExpectedTankValues', 'https://static.modxvm.com/wn8-data-exp/json/wn8exp.json')
            try:
                expfile = json.load(open(self.expectedValuesPath))
                verfile = json.dumps(expfile['header']['version'])
            except:
                verfile = ''
                print '[mod_stat] No valid expected_tank_values.json found, trying ' + expurl + '.'
            try:
                expdata = json.load(urllib2.urlopen(expurl, timeout=3))
                verdata = json.dumps(expdata['header']['version'])
                if verfile != verdata:
                    urllib.urlretrieve(expurl, self.expectedValuesPath)
                    print '[mod_stat] expected_tank_values.json updated to ' + verdata + '.'
                    if self.config.get('updateInfoExpectedTankValues', True):
                        SystemMessages.pushMessage("<font color='#BFE9FF'>Yasen</font><font color='#FF3333'>Krasen</font> Info!\n\nExpected Tank Values updated to:\n" + verdata + "\n", type=SystemMessages.SM_TYPE.Warning)
            except:
                print '[mod_stat] Unable to access ' + expurl + '.'

        with open(self.expectedValuesPath) as origExpectedValuesJson:
            origExpectedValues = json.load(origExpectedValuesJson)
            for tankValues in origExpectedValues['data']:
                idNum = int(tankValues.pop('IDNum'))
                self.expectedValues[idNum] = {}
                for key in ['expDamage', 'expFrag', 'expSpot', 'expDef', 'expWinRate']:
                    self.expectedValues[idNum][key] = float(tankValues[key])
        invalidCache = True
        if os.path.isfile(self.statCacheFilePath):
            with open(self.statCacheFilePath) as jsonCache:
                self.cache = json.load(jsonCache)
                self.startDate = self.cache.get('date', self.getWorkDate())
                if self.cache.get('version', 0) == self.cacheVersion and \
                    (self.startDate == self.getWorkDate() or \
                    not self.config.get('dailyAutoReset', True)) and \
                    not self.config.get('clientReloadReset', False):
                    if self.cache.get('players', {}).has_key(self.playerName):
                        self.battles = self.cache['players'][self.playerName]['battles']
                    invalidCache = False
        if invalidCache:
            self.cache = {}
        if self.config.get('checkForUpdate', True):
            try:
                file = urllib2.urlopen('https://pastebin.com/raw/qLxFKQUV')
                data = file.read()
                file.close()
                dom = parseString(data)
                try:
                    latestVersion = dom.getElementsByTagName('version')[0].firstChild.data
                except:
                    latestVersion = ''
                if latestVersion != VERSION and latestVersion != '':
                    try:
                        updateDetails = dom.getElementsByTagName('details')[0].firstChild.data
                    except:
                        updateDetails = ''
                    SystemMessages.pushMessage("<font color='#BFE9FF'>Yasen</font><font color='#FF3333'>Krasen</font> Update!\n" + updateDetails + "\n<font color='#C5AB5D'>" + latestVersion + " is available at <a href='event:" + URLLINK + "'>here</a>.</font>\n", type=SystemMessages.SM_TYPE.GameGreeting)
                else:
                    try:
                        infoMessage = dom.getElementsByTagName('info')[0].firstChild.data
                    except:
                        infoMessage = ''
                    if infoMessage != '':
                        SystemMessages.pushMessage("<font color='#BFE9FF'>Yasen</font><font color='#FF3333'>Krasen</font> Info!\n\n" + infoMessage + "\n", type=SystemMessages.SM_TYPE.GameGreeting)
            except:
                print '[mod_stat] Unable to access remote update file.'
        self.updateMessage()

    def readConfig(self):
        with codecs.open(self.configFilePath, 'r', 'utf-8-sig') as configFileJson:
            try:
                self.config = json.load(configFileJson)
                self.battleStatPatterns = []
                for pattern in self.config.get('battleStatPatterns',[]):
                    try:
                        condition = pattern.get('if', 'True')
                        condition = re.sub('{{(\w+)}}', 'values[\'\\1\']', condition)
                    except:
                        print '[mod_stat] Invalid condition ' + pattern.get('if','')
                        continue
                    try:
                        compiled = re.compile(pattern.get('pattern',''))
                        self.battleStatPatterns.append({
                            'condition': condition,
                            'pattern': compiled,
                            'repl': pattern.get('repl','')
                        })
                    except:
                        print '[mod_stat] Invalid pattern ' + pattern.get('pattern','')
                        continue
                self.configIsValid = True
            except:
                print '[mod_stat] load config.json has failed'
                self.config = {}
                self.configIsValid = False

    def getWorkDate(self):
        return datetime.date.today().strftime('%Y-%m-%d') \
            if datetime.datetime.now().hour >= self.config.get('dailyAutoResetHour', 4) \
            else (datetime.date.today() - datetime.timedelta(days = 1)).strftime('%Y-%m-%d')

    def save(self):
        statCache = open(self.statCacheFilePath, 'w')
        self.cache['version'] = self.cacheVersion
        self.cache['date'] = self.startDate
        if not self.cache.has_key('players'):
            self.cache['players'] = {}
        if not self.cache['players'].has_key(self.playerName):
            self.cache['players'][self.playerName] = {}
        self.cache['players'][self.playerName]['battles'] = self.battles
        statCache.write(json.dumps(self.cache, sort_keys = True, indent = 4, separators=(',', ': ')))
        statCache.close()

    def createMessage(self):
        messages = {GENERAL: self.messageGeneral, BY_TANK: self.messageByTank}
        msg = messages[self.page]
        message = {
            'typeID': 1,
            'message': {
                'bgIcon': self.bgIcon,
                'defaultIcon': '',
                'savedData': 0,
                'timestamp': -1,
                'filters': [],
                'buttonsLayout': [],
                'message': msg,
                'type': 'black',
                'icon': self.config.get('icon', '')
            },
            'entityID': 99999,
            'auxData': ['GameGreeting']
        }
        return message

    def battleResultsCallback(self, arenaUniqueID, responseCode, value = None, revision = 0):
        if responseCode == AccountCommands.RES_NON_PLAYER or responseCode == AccountCommands.RES_COOLDOWN:
            BigWorld.callback(1.0, lambda: self.queue.put(arenaUniqueID))
            self.battleResultsBusy.release()
            return
        if responseCode < 0:
            self.battleResultsBusy.release()
            return
        arenaTypeID = value['common']['arenaTypeID']
        arenaType = ArenaType.g_cache[arenaTypeID]
        personal = value['personal'].itervalues().next()
        vehicleCompDesc = personal['typeCompDescr']
        arenaName = i18n.makeString(arenaType.name)
        vt = vehiclesWG.getVehicleType(vehicleCompDesc)
        result = 1 if int(personal['team']) == int(value['common']['winnerTeam'])\
            else (0 if not int(value['common']['winnerTeam']) else -1)
        death = 1 if int(personal['deathReason']) > -1 else 0
        place = 1
        arenaUniqueID = value['arenaUniqueID']
        squadsTier = {}
        vehicles = value['vehicles']
        for vehicle in vehicles.values():
            pTypeCompDescr = vehicle[0]['typeCompDescr']
            if pTypeCompDescr is not None:
                pvt = vehiclesWG.getVehicleType(pTypeCompDescr)
                tier = pvt.level
                if set(vehiclesWG.VEHICLE_CLASS_TAGS.intersection(pvt.tags)).pop() == 'lightTank' and tier > 5:
                    tier += 1
                try:
                    squadID = value['players'][vehicle[0]['accountDBID']]['prebattleID']
                except:
                    squadID = 0
                squadsTier[squadID] = max(squadsTier.get(squadID, 0), tier)
            if personal['team'] == vehicle[0]['team'] and personal['originalXP'] < vehicle[0]['xp']:
                place += 1
        battleTier = max(squadsTier.values())
        proceeds = personal['credits'] - personal['autoRepairCost'] -\
                   personal['autoEquipCost'][0] - personal['autoLoadCost'][0]
        tmenXP = personal['tmenXP']
        if 'premium' in vt.tags:
            tmenXP = int(1.5 * tmenXP)
        battle = {
            'idNum': vehicleCompDesc,
            'map': arenaType.geometryName,
            'vehicle': vt.name.replace(':', '-'),
            'tier': vt.level,
            'result': result,
            'dailyXPFactor': personal['dailyXPFactor10'] / 10,
            'damage': personal['damageDealt'],
            'damageRec': personal['damageReceived'],
            'potDamageRec': personal['potentialDamageReceived'],
            'damageBlocked': personal['damageBlockedByArmor'],
            'deathsCount': death,
            'frag': personal['kills'],
            'mileage': personal['mileage'],
            'spot': personal['spotted'],
            'def': personal['droppedCapturePoints'],
            'cap': personal['capturePoints'],
            'shots': personal['shots'],
            'hits': personal['directHits'],
            'pierced': personal['piercings'],
            'xp': personal['xp'],
            'originalXP': personal['originalXP'],
            'place': place,
            'originalPremXP': round(personal['originalXP'] * personal['premiumXPFactor10'] / 10),
            'freeXP': personal['freeXP'],
            'originalFreeXP': personal['originalFreeXP'],
            'tmenXP': tmenXP,
            'eventTmenXP': personal['eventTMenXP'],
            'autoRepairCost': personal['autoRepairCost'],
            'autoLoadCost': personal['autoLoadCost'][0],
            'autoEquipCost': personal['autoEquipCost'][0],
            'service': personal['autoEquipCost'][0] + personal['autoLoadCost'][0] + personal['autoRepairCost'],
            'grossCredits': personal['credits'],
            'netCredits': proceeds,
            'crystal': personal['crystal'],
            'grossGold': personal['gold'],
            'netGold': personal['gold'] - personal['autoEquipCost'][1] - personal['autoLoadCost'][1],
            'battleTier': battleTier,
            'damageAssistedRadio': personal['damageAssistedRadio'],
            'damageAssistedTrack': personal['damageAssistedTrack'],
            'damageAssistedStun': personal['damageAssistedStun'],
            'stunDuration': personal['stunDuration'],
            'stunNum': personal['stunNum'],
            'stunned': personal['stunned'],
            'assist': personal['damageAssistedRadio'] + personal['damageAssistedTrack']
        }
        extended = {
            'vehicle-raw': battle['vehicle'],
            'vehicle-short': vt.shortUserString,
            'vehicle-long': vt.userString,
            'map-raw': battle['map'],
            'map': arenaName,
            'result': result,
            'autoRepair': personal['autoRepairCost'],
            'autoEquip': personal['autoEquipCost'][0],
            'autoLoad': personal['autoLoadCost'][0]
        }
        if self.config.get('dailyAutoReset', True) and self.startDate != stat.getWorkDate():
            self.reset()
        if value['common']['bonusType'] in self.config.get('battleType', [1]):
            self.battles.append(battle)
            self.save()
            self.updateMessage()
        battleStat, gradient, palette = self.calcWN8([battle])
        extGradient, extPalette = self.refreshColorMacros(extended)
        gradient.update(extGradient)
        palette.update(extPalette)
        self.battleStats[arenaUniqueID] = {}
        self.battleStats[arenaUniqueID]['values'] = battleStat
        self.battleStats[arenaUniqueID]['extendedValues'] = extended
        self.battleStats[arenaUniqueID]['gradient'] = gradient
        self.battleStats[arenaUniqueID]['palette'] = palette
        self.battleResultsBusy.release()

    def reset(self):
        self.page = GENERAL
        self.startDate = self.getWorkDate()
        self.battles = []
        self.save()
        self.updateMessage()

    def mainLoop(self):
        while True:
            arenaUniqueID = self.queue.get()
            self.battleResultsAvailable.wait()
            self.battleResultsBusy.acquire()
            BigWorld.player().battleResultsCache.get(arenaUniqueID,\
                lambda resID, value: self.battleResultsCallback(arenaUniqueID, resID, value, None))

    def refreshColorMacros(self, values):
        gradient = {}
        palette = {}
        if values.get('battlesCount', 1) == 0:
            for key in values.keys():
                gradient[key] = '#FFFFFF'
                palette[key] = '#FFFFFF'
            return (gradient, palette)
        for key in values.keys():
            if self.config.get('gradient', {}).has_key(key):
                colors = self.config.get('gradient', {})[key]
                if values[key] <= colors[0]['value']:
                    gradient[key] = colors[0]['color']
                elif values[key] >= colors[-1]['value']:
                    gradient[key] = colors[-1]['color']
                else:
                    sVal = colors[0]['value']
                    eVal = colors[1]['value']
                    i = 1
                    while eVal < values[key]:
                        sVal = colors[i]['value']
                        i += 1
                        eVal = colors[i]['value']
                    val = float(values[key] - sVal) / (eVal - sVal)
                    gradient[key] = gradColor(colors[i - 1]['color'], colors[i]['color'], val)
            else:
                gradient[key] = '#FFFFFF'
            if self.config.get('palette', {}).has_key(key):
                colors = self.config.get('palette', {})[key]
                palette[key] = colors[-1]['color']
                for item in reversed(colors):
                    if values[key] < item['value']:
                        palette[key] = item['color']
                    else:
                        break
            else:
                palette[key] = '#FFFFFF'
        return (gradient, palette)

    def calcExpected(self, newIdNum):
        v = vehiclesWG.getVehicleType(newIdNum)
        newTier = v.level
        newType = set(vehiclesWG.VEHICLE_CLASS_TAGS.intersection(v.tags)).pop()
        if newTier < 1 or newTier > 10:
            newTier = 10
        tierExpected = {}
        tierExpectedCount = 0.0
        typeExpected = {}
        typeExpectedCount = 0.0
        for idNum in self.expectedValues:
            try:
                vt = vehiclesWG.getVehicleType(idNum)
            except:
                continue
            if vt.level == newTier:
                tierExpectedCount += 1
                vType = set(vehiclesWG.VEHICLE_CLASS_TAGS.intersection(vt.tags)).pop()
                if vType == newType:
                    typeExpectedCount += 1
                for key in self.expectedValues[idNum]:
                    tierExpected[key] = tierExpected.get(key, 0) + self.expectedValues[idNum].get(key, 0.0)
                    if vType == newType:
                        typeExpected[key] = typeExpected.get(key, 0) + self.expectedValues[idNum].get(key, 0.0)
        if typeExpectedCount > 0:
            for key in typeExpected:
                typeExpected[key] /= typeExpectedCount
            self.expectedValues[newIdNum] = typeExpected.copy()
            return
        for key in tierExpected:
            tierExpected[key] /= tierExpectedCount
        self.expectedValues[newIdNum] = tierExpected.copy()

    def xeff(self, x):
        if x > 2300:
            return 100
        return int(max(0, min(100, x * (x * (x * (x * (x * (x * 6.449e-18 - 4.089e-14) + 8.302e-11) - 4.433e-08) - 4.82e-05) + 0.1257) - 40.42)))

    def xwn8(self, x):
        if x > 3800:
            return 100
        return int(max(0, min(100, x * (x * (x * (x * (x * (-x * 9.762e-20 + 1.6221e-15) - 1.007e-11) + 2.7916e-08) - 3.6982e-05) + 0.05577) - 1.3)))

    def calcWN8(self, battles):
        values = {}
        values['battlesCount'] = len(battles)
        totalTier = 0
        totalPlace = 0
        places = []
        totalBattleTier = 0
        valuesKeys = ['winsCount', 'defeatsCount', 'drawsCount', 'dailyXPFactor', 'totalDmg', 'totalDmgRec', 'totalMileage', 'totalMileagekm', 'totalPotDmgRec', 'totalDamageBlocked', 'totalDeathsCount', 'totalFrag', 'totalShots', 'totalHits', 'totalPierced', 'totalSpot', 'totalDef', 'totalCap',\
            'totalAssist', 'totalDmgAssistTrack', 'totalDmgAssistRadio', 'totalDmgAssistedStun', 'totalStunDuration', 'totalStunNum', 'totalStunned', 'totalXP', 'allXP', 'totalOriginXP', 'totalFreeXP', 'totalOriginalFreeXP', 'totalOriginPremXP', 'totalTmenXP', 'totalEventTmenXP', 'autoRepairCost',\
            'autoLoadCost', 'autoEquipCost', 'service', 'grossCredits', 'netCredits', 'totalCrystal', 'grossGold', 'netGold', 'autoRepairGBMCost', 'autoLoadGBMCost', 'autoEquipGBMCost', 'place']
        for key in valuesKeys:
            values[key] = 0
        expKeys = ['expDamage', 'expFrag', 'expSpot', 'expDef', 'expWinRate']
        expValues = {}
        for key in expKeys:
            expValues['total_' + key] = 0.0
        resCounters = {-1: 'defeatsCount', 0: 'drawsCount', 1: 'winsCount'}
        for battle in battles:
            values[resCounters[battle['result']]] += 1
            values['totalDmg'] += battle['damage']
            values['totalDmgRec'] += battle['damageRec']
            values['totalPotDmgRec'] += battle['potDamageRec']
            values['totalDamageBlocked'] += battle['damageBlocked']
            values['totalDeathsCount'] += battle['deathsCount']
            values['totalFrag'] += battle['frag']
            values['totalSpot'] += battle['spot']
            values['totalDef'] += battle['def']
            values['totalCap'] += battle['cap']
            values['totalShots'] += battle['shots']
            values['totalHits'] += battle['hits']
            values['totalPierced'] += battle['pierced']
            values['totalAssist'] += battle['assist']
            values['totalDmgAssistTrack'] += battle['damageAssistedTrack']
            values['totalDmgAssistRadio'] += battle['damageAssistedRadio']
            values['totalDmgAssistedStun'] += battle['damageAssistedStun']
            values['totalStunDuration'] += battle['stunDuration']
            values['totalStunNum'] += battle['stunNum']
            values['totalStunned'] += battle['stunned']
            values['totalXP'] += battle['xp']
            values['allXP'] += battle['xp'] + battle['freeXP']
            values['totalOriginXP'] += battle['originalXP']
            values['totalOriginPremXP'] += int(battle['originalPremXP'])
            values['totalFreeXP'] += battle['freeXP']
            values['totalOriginalFreeXP'] += battle['originalFreeXP']
            values['totalTmenXP'] += battle['tmenXP']
            values['totalEventTmenXP'] += battle['eventTmenXP']
            values['totalMileage'] += battle['mileage']
            values['totalMileagekm'] += battle['mileage']/float(1000)
            values['autoRepairCost'] = battle['autoRepairCost']
            values['autoLoadCost'] = battle['autoLoadCost']
            values['autoEquipCost'] = battle['autoEquipCost']
            values['autoRepairGBMCost'] = battle['autoRepairCost']
            values['autoLoadGBMCost'] = battle['autoLoadCost']
            values['autoEquipGBMCost'] = battle['autoEquipCost']
            values['service'] += battle['service']
            values['netCredits'] += battle['netCredits']
            values['grossCredits'] += battle['grossCredits']
            values['totalCrystal'] += battle['crystal']
            values['grossGold'] += battle['grossGold']
            values['netGold'] += battle['netGold']
            values['place'] = battle['place']
            values['dailyXPFactor'] = battle['dailyXPFactor']
            totalTier += battle['tier']
            totalBattleTier += battle['battleTier']
            totalPlace += battle['place']
            places.append(battle['place'])
            idNum = battle['idNum']
            if not self.expectedValues.has_key(idNum):
                self.calcExpected(idNum)
            expValues['total_expDamage'] += self.expectedValues[idNum]['expDamage']
            expValues['total_expFrag'] += self.expectedValues[idNum]['expFrag']
            expValues['total_expSpot'] += self.expectedValues[idNum]['expSpot']
            expValues['total_expDef'] += self.expectedValues[idNum]['expDef']
            expValues['total_expWinRate'] += self.expectedValues[idNum]['expWinRate']
        if values['battlesCount'] > 0:
            values['avgWinRate'] = float(values['winsCount'])/values['battlesCount']*100
            values['avgDamage'] = float(values['totalDmg'])/values['battlesCount']
            values['avgDamageRec'] = int(values['totalDmgRec']/values['battlesCount'])
            values['avgPotDmgRec'] = int(values['totalPotDmgRec']/values['battlesCount'])
            values['avgDamageBlocked'] = int(values['totalDamageBlocked']/values['battlesCount'])
            values['avgDeathsCount'] = 0 if values['totalDeathsCount'] < 1 else float(values['totalDeathsCount'])/values['battlesCount']
            values['avgFrag'] = float(values['totalFrag'])/values['battlesCount']
            values['avgShots'] = float(values['totalShots'])/values['battlesCount']
            values['hitsRate'] = 0 if values['totalShots'] < 1 else float(values['totalHits'])/values['totalShots']*100
            values['deathsRate'] = 0 if values['totalDeathsCount'] < 1 else float(values['totalDeathsCount'])/values['battlesCount']*100
            values['survivalRate'] = 100 if values['totalDeathsCount'] < 1 else abs(float(values['totalDeathsCount'])/values['battlesCount']*100-100)
            values['effHitsRate'] = 0 if values['totalHits'] < 1 else float(values['totalPierced'])/values['totalHits']*100
            values['avgMileage'] = float(values['totalMileage'])/values['battlesCount']
            values['avgMileagekm'] = float((values['totalMileage'])/values['battlesCount'])/1000
            values['avgSpot'] = float(values['totalSpot'])/values['battlesCount']
            values['avgDef'] = float(values['totalDef'])/values['battlesCount']
            values['avgCap'] = float(values['totalCap'])/values['battlesCount']
            values['avgAssist'] = int(values['totalAssist'])/values['battlesCount']
            values['avgDmgAssistTrack'] = int(values['totalDmgAssistTrack'])/values['battlesCount']
            values['avgDmgAssistRadio'] = int(values['totalDmgAssistRadio'])/values['battlesCount']
            values['avgDmgAssistedStun'] = int(values['totalDmgAssistedStun'])/values['battlesCount']
            values['avgStunDuration'] = int(values['totalStunDuration'])/values['battlesCount']
            values['avgStunNum'] = int(values['totalStunNum'])/values['battlesCount']
            values['avgStunned'] = int(values['totalStunned'])/values['battlesCount']
            values['avgXP'] = int(values['totalXP']/values['battlesCount'])
            values['avgOriginalXP'] = int(values['totalOriginXP']/values['battlesCount'])
            values['avgOriginalPremXP'] = int(values['totalOriginPremXP']/values['battlesCount'])
            values['avgFreeXP'] = int(values['totalFreeXP']/values['battlesCount'])
            values['avgOriginalFreeXP'] = int(values['totalOriginalFreeXP']/values['battlesCount'])
            values['avgTmenXP'] = int(values['totalTmenXP']/values['battlesCount'])
            values['avgEventTmenXP'] = int(values['totalEventTmenXP']/values['battlesCount'])
            values['avgNetCredits'] = int(values['netCredits']/values['battlesCount'])
            values['avgGrossCredits'] = int(values['grossCredits']/values['battlesCount'])
            values['avgCrystal'] = int(values['totalCrystal'] / values['battlesCount'])
            values['avgService'] = int(values['service'] / values['battlesCount'])
            values['avgTier'] = float(totalTier)/values['battlesCount']
            values['avgBattleTier'] = float(totalBattleTier)/values['battlesCount']
            values['avgPlace'] = round(float(totalPlace)/values['battlesCount'], 1)
            places = sorted(places)
            length = len(places)
            values['medPlace'] = (places[length/2] +places[length/2 - 1])/2.0  if not length % 2\
                else float(places[length/2])
            for key in expKeys:
                values[key] = expValues['total_' + key]/values['battlesCount']
            values['WN6'] = max(0, int((1240 - 1040/(min(values['avgTier'], 6))**0.164)*values['avgFrag'] + \
                values['avgDamage']*530/(184*math.exp(0.24*values['avgTier']) + 130) + \
                values['avgSpot']*125 + min(values['avgDef'], 2.2)*100 + \
                ((185/(0.17 + math.exp((values['avgWinRate'] - 35)* -0.134))) - 500)*0.45 + \
                (6-min(values['avgTier'], 6))*-60))
            values['XWN6'] = 100 if values['WN6'] > 2350 \
                else int(max(min(values['WN6']*(values['WN6']*(values['WN6']*(values['WN6']*\
                (values['WN6']*(-0.000000000000000000852*values['WN6'] + 0.000000000000008649) - \
                0.000000000039744) + 0.00000008406) - 0.00007446) + 0.06904) - 6.19, 100), 0))
            values['WN7'] = max(0, int((1240 - 1040/(min(values['avgTier'], 6))**0.164)*values['avgFrag'] + \
                values['avgDamage']*530/(184*math.exp(0.24*values['avgTier']) + 130) + \
                values['avgSpot']*125*(min(values['avgTier'], 3))/3 + min(values['avgDef'], 2.2)*100 + \
                ((185/(0.17 + math.exp((values['avgWinRate'] - 35)* -0.134))) - 500)*0.45 - \
                ((5-min(values['avgTier'], 5))*125) / \
                (1+math.exp((values['avgTier'] - (values['battlesCount']/220)**(3/values['avgTier']))*1.5)) ))
            values['XWN7'] = 100 if values['WN7'] > 2350 \
                else int(max(min(values['WN7']*(values['WN7']*(values['WN7']*(values['WN7']*\
               (values['WN7']*(0.000000000000000001641 * values['WN7'] - 0.0000000000000126) + \
               0.00000000003223) - 0.00000003793) + 0.00003139) + 0.02747) - 1.92, 100), 0))
            values['EFF'] = max(0, int(values['avgDamage']*(10/(values['avgTier'] + 2)) *\
                (0.23 + 2*values['avgTier']/100) + values['avgFrag'] * 250 + \
                values['avgSpot'] * 150 + math.log(values['avgCap'] + 1, 1.732) * 150 + \
                values['avgDef'] * 150))
            values['XEFF'] = self.xeff(values['EFF'])
            values['BR'] = max(0, int(values['avgDamage']*(0.2 + 1.5/values['avgTier']) + \
                values['avgFrag'] * (350 - values['avgTier'] * 20) + \
                ((values['avgDmgAssistRadio']/2)*(0.2 + 1.5/values['avgTier'])) + \
                ((values['avgDmgAssistTrack']/2)*(0.2 + 1.5/values['avgTier'])) + \
                values['avgSpot'] * 200 + values['avgCap'] * 15 + values['avgDef'] * 15 ))
        else:
            for key in ['avgWinRate', 'avgDamage', 'avgDamageRec', 'avgMileage', 'avgMileagekm', 'avgPotDmgRec', 'avgDamageBlocked', 'survivalRate', 'deathsRate', 'avgDeathsCount', 'avgFrag', 'avgShots', 'hitsRate',\
                'effHitsRate', 'avgSpot', 'avgDef', 'avgCap', 'avgAssist', 'avgDmgAssistTrack', 'avgDmgAssistRadio', 'avgDmgAssistedStun', 'avgStunDuration', 'avgStunNum', 'avgStunned', 'avgXP', 'avgOriginalXP',\
                'avgOriginalPremXP', 'avgFreeXP', 'avgOriginalFreeXP', 'avgTmenXP', 'avgEventTmenXP', 'avgNetCredits', 'avgGrossCredits', 'avgCrystal', 'avgService', 'avgTier', 'avgBattleTier', 'medPlace', 'avgPlace',\
                'WN6', 'XWN6', 'WN7', 'XWN7', 'EFF', 'XEFF', 'BR']:
                values[key] = 0
            for key in expKeys:
                values[key] = 1
        values['avgBattleTierDiff'] = values['avgBattleTier'] - values['avgTier']
        values['rDAMAGE'] = values['avgDamage']/values['expDamage']
        values['rSPOT'] = values['avgSpot']/values['expSpot']
        values['rFRAG'] = values['avgFrag']/values['expFrag']
        values['rDEF'] = values['avgDef']/values['expDef']
        values['rWIN'] = values['avgWinRate']/values['expWinRate']
        values['rWINc'] = max(0, (values['rWIN'] - 0.71)/(1 - 0.71))
        values['rDAMAGEc'] = max(0, (values['rDAMAGE'] - 0.22)/(1 - 0.22))
        values['rFRAGc'] = max(0, min(values['rDAMAGEc'] + 0.2, (values['rFRAG'] - 0.12)/(1 - 0.12)))
        values['rSPOTc'] = max(0, min(values['rDAMAGEc'] + 0.1, (values['rSPOT'] - 0.38)/(1 - 0.38)))
        values['rDEFc'] = max(0, min(values['rDAMAGEc'] + 0.1, (values['rDEF'] - 0.10)/(1 - 0.10)))
        values['WN8'] = 980*values['rDAMAGEc'] + 210*values['rDAMAGEc']*values['rFRAGc'] + \
            155*values['rFRAGc']*values['rSPOTc'] + 75*values['rDEFc']*values['rFRAGc'] + \
            145*min(1.8, values['rWINc'])
        values['XWN8'] = self.xwn8(values['WN8'])
        values['WN8'] = int(values['WN8'])
        values['avgDamage'] = int(values['avgDamage'])
        values['avgMileage'] = int(values['avgMileage'])
        gradient, palette = self.refreshColorMacros(values)
        return (values, gradient, palette)

    def applyMacros(self, val, prec = 2):
        if type(val) == str:
            return val
        if prec <= 0:
            return format(int(round(val)), ',d')
        sVal = format(val, ',.%sf' % prec) \
            if type(val) is float else format(val, ',d')
        separator = self.config.get('thousandSeparator', ' ')
        sVal = sVal.replace(',', separator)
        return sVal

    def applyMacros2(self, val, width, prec = 0):
        if type(val) == str:
            return val
        if prec <= 0:
            sVal = format(val, '>%s,' % width)
        sVal = format(val, '>%s,.%sf' % (width, prec))
        separator = self.config.get('thousandSeparator', ' ')
        sVal = sVal.replace(',', separator)
        return sVal

    def formatString(self, text, values, gradient, palette):
        for key in values.keys():
            text = text.replace('{{%s}}' % key, self.applyMacros(values[key]))
            text = text.replace('{{%s:d}}' % key, self.applyMacros(values[key], 0))
            text = text.replace('{{%s:1f}}' % key, self.applyMacros(values[key], 1))
            for xx in xrange(1,20):
                text = text.replace('{{%s:%d}}' % (key, xx), self.applyMacros2(values[key], xx))
                text = text.replace('{{%s:%d.1f}}' % (key, xx), self.applyMacros2(values[key], xx, 1))
                text = text.replace('{{%s:%d.2f}}' % (key, xx), self.applyMacros2(values[key], xx, 2))
            text = text.replace('{{g:%s}}' % key, gradient[key])
            text = text.replace('{{c:%s}}' % key, palette[key])
        return text

    def updateMessage(self):
        if not self.configIsValid:
            self.message = 'config.json is not valid'
            return
        self.values, self.gradient, self.palette = self.calcWN8(self.battles)
        bg = self.config.get('statBackground', '')
        self.bgIcon = self.formatString(bg, self.values, self.gradient, self.palette)
        msg = '\n'.join(self.config.get('template',''))
        userMacros = self.config.get('userMacros', {})
        for key in userMacros.keys():
            msg = msg.replace('{{%s}}' % key, userMacros[key])
        msg = msg.replace('{{buttonGeneral}}', '<a href="event:yk-stat:buttonGeneral">' + self.config.get('buttonGeneral', 'General') + '</a>')
        msg = msg.replace('{{buttonTank}}', '<a href="event:yk-stat:buttonTank">' + self.config.get('buttonTank', 'by Tank') + '</a>')
        msg = msg.replace('{{buttonReset}}', '<a href="event:yk-stat:buttonReset">' + self.config.get('buttonReset', 'Reset') + '</a>')
        msg = self.formatString(msg, self.values, self.gradient, self.palette)
        self.messageGeneral = msg

        if len(self.battles) and self.config.get('enableByTank', True):
            msg = self.config.get('byTankTitle','')
            tankStat = {}
            for battle in self.battles:
                idNum = battle['idNum']
                if tankStat.has_key(idNum):
                    tankStat[idNum].append(battle)
                else:
                    tankStat[idNum] = [battle]
            tankValues = {}
            tankGradient = {}
            tankPalette = {}
            row = self.config.get('byTankStats','')
            sorting = self.config.get('sortReverse', True)
            tankMacro = self.config.get('sortMacro', 'WN8')
            for idNum in tankStat.keys():
                values, gradient, palette = self.calcWN8(tankStat[idNum])
                tankValues[idNum] = values
                tankGradient[idNum] = gradient
                tankPalette[idNum] = palette
            for idNum in sorted(tankValues.keys(), key = lambda value: tankValues[value][tankMacro], reverse = sorting):
                row = self.config.get('byTankStats','')
                vt = vehiclesWG.getVehicleType(idNum)
                row = row.replace('{{vehicle-long}}', vt.userString)
                row = row.replace('{{vehicle-short}}', vt.shortUserString)
                row = row.replace('{{vehicle-raw}}', vt.name.replace(':', '-'))
                row = self.formatString(row, tankValues[idNum], tankGradient[idNum], tankPalette[idNum])
                msg += '\n' + row
            msg += self.config.get('byTankButton','')
            userMacros = self.config.get('userMacros', {})
            for key in userMacros.keys():
                msg = msg.replace('{{%s}}' % key, userMacros[key])
            msg = msg.replace('{{buttonGeneral}}', '<a href="event:yk-stat:buttonGeneral">' + self.config.get('buttonGeneral', 'General') + '</a>')
            msg = msg.replace('{{buttonTank}}', '<a href="event:yk-stat:buttonTank">' + self.config.get('buttonTank', 'by Tank') + '</a>')
            msg = msg.replace('{{buttonReset}}', '<a href="event:yk-stat:buttonReset">' + self.config.get('buttonReset', 'Reset') + '</a>')
            self.messageByTank = msg
        else:
            self.messageByTank = ''

    def replaceBattleResultMessage(self, message, arenaUniqueID):
        message = unicode(message, 'utf-8')
        if self.config.get('debugBattleResultMessage', False):
            LOG_NOTE(message)
        basicValues = self.battleStats[arenaUniqueID]['values']
        extendedValues = self.battleStats[arenaUniqueID]['extendedValues']
        values = basicValues
        values.update(extendedValues)
        for pattern in self.battleStatPatterns:
            try:
                if not eval(pattern.get('condition')):
                    continue
            except:
                print '[mod_stat] Invalid calculation condition ' + pattern.get('condition')
                continue
            message = re.sub(pattern.get('pattern',''), pattern.get('repl',''), message)
        battleStatText = ''.join(self.config.get('battleStatText',''))
        gradient = self.battleStats[arenaUniqueID]['gradient']
        palette = self.battleStats[arenaUniqueID]['palette']
        userMacros = self.config.get('userMacros', {})
        for key in userMacros.keys():
            if key in ['dailyXP'] and values[key + 'Factor'] == 1:
                battleStatText = battleStatText.replace('{{%s}}' % key, '')
            if key in ['autoRepair', 'autoLoad', 'autoEquip', 'autoRepairGBM', 'autoLoadGBM', 'autoEquipGBM'] and values[key + 'Cost'] == 0:
                battleStatText = battleStatText.replace('{{%s}}' % key, '')
            else:
                battleStatText = battleStatText.replace('{{%s}}' % key, userMacros[key])
        message = message + '<font color=\'#929290\'>' + battleStatText + '</font>'
        message = self.formatString(message, values, gradient, palette)
        return message

    def filterNotificationList(self, item):
        message = item['message'].get('message', '')
        msg = unicode(message, 'utf-8') if isinstance(message, str) \
            else message if isinstance(message, unicode) else None
        if msg:
            for pattern in self.config.get('hideMessagePatterns', []):
                if re.search(pattern, msg, re.I):
                    return False
        return True

    def expandStatNotificationList(self, item):
        savedData = item['message'].get('savedData', -1)
        arenaUniqueID = -1
        if isinstance(savedData, long):
            arenaUniqueID = int(savedData)
        elif isinstance(savedData, tuple):
            arenaUniqueID = int(savedData[0])
        message = item['message'].get('message', '')
        if arenaUniqueID > 0 and self.battleStats.has_key(arenaUniqueID) and type(message) == str:
            message = self.replaceBattleResultMessage(message, arenaUniqueID)
            item['message']['message'] = message
            if self.config.get('overwriteBattleResultBgIcon', False):
                result = self.battleStats[arenaUniqueID]['extendedValues']['result']
                bgIconKeys = {-1: 'bgIconDefeat', 0: 'bgIconDraw', 1: 'bgIconWin'}
                bgIconKey = bgIconKeys[result]
                bgIcon = self.config.get(bgIconKey, item['message']['bgIcon'])
                item['message']['bgIcon'] = bgIcon
        return item

old_onBecomePlayer = Account.onBecomePlayer

def new_onBecomePlayer(self):
    old_onBecomePlayer(self)
    stat.battleResultsAvailable.set()
    stat.load()

Account.onBecomePlayer = new_onBecomePlayer

old_onBecomeNonPlayer = Account.onBecomeNonPlayer

def new_onBecomeNonPlayer(self):
    stat.battleResultsAvailable.clear()
    old_onBecomeNonPlayer(self)

Account.onBecomeNonPlayer = new_onBecomeNonPlayer

old_nlv_getMessagesList = NotificationListView._NotificationListView__getMessagesList

def new_nlv_getMessagesList(self):
    result = old_nlv_getMessagesList(self)
    if stat.config.get('onlineReloadConfig', False):
        stat.readConfig()
        stat.updateMessage()
        stat.config['onlineReloadConfig'] = True
    if self._NotificationListView__currentGroup in 'info':
        result.append(stat.createMessage())
    return result

NotificationListView._NotificationListView__getMessagesList = new_nlv_getMessagesList

from notification.settings import NOTIFICATION_GROUP

old_nlv_setNotificationList = NotificationListView._NotificationListView__setNotificationList

def new_nlv_setNotificationList(self):
    if stat.config.get('onlineReloadConfig', False):
        stat.readConfig()
        stat.updateMessage()
        stat.config['onlineReloadConfig'] = True
    formedList = self._NotificationListView__getMessagesList()
    if len(stat.config.get('hideMessagePatterns', [])):
        formedList = filter(stat.filterNotificationList, formedList)
    if stat.config.get('showStatForBattle', True):
        formedList = map(stat.expandStatNotificationList, formedList)
    self.as_setMessagesListS({'messages': formedList,
         'emptyListText': self._NotificationListView__getEmptyListMsg(len(formedList) > 0),
         'btnBarSelectedIdx': NOTIFICATION_GROUP.ALL.index(self._NotificationListView__currentGroup)})
    self._model.resetNotifiedMessagesCount(self._NotificationListView__currentGroup)

NotificationListView._NotificationListView__setNotificationList = new_nlv_setNotificationList

old_nlv_onClickAction = NotificationListView.onClickAction
old_npuv_onClickPopup = NotificationPopUpViewer.onClickAction

def new_onClickAction(self, typeID, entityID, action):
    if action == URLLINK:
        BigWorld.wg_openWebBrowser(action)
    elif 'yk-stat:' in action:
        if action.split(':')[1] == 'buttonGeneral':
            stat.page = GENERAL
        elif action.split(':')[1] == 'buttonTank' and stat.messageByTank != '':
            stat.page = BY_TANK
        elif action.split(':')[1] == 'buttonReset':
            BigWorld.callback(0, lambda: showConfirmDialog('Are you sure to reset session statistics?', lambda result: doReset(self, result)))
        self.as_updateMessageS(stat.createMessage())
    else:
        old_nlv_onClickAction(self, typeID, entityID, action)

def doReset(nlv, confirmed):
    if confirmed:
        stat.reset()
        nlv.as_updateMessageS(stat.createMessage())

def new_onClickPopup(self, typeID, entityID, action):
    if action == URLLINK:
        BigWorld.wg_openWebBrowser(action)
    else:
        old_npuv_onClickPopup(self, typeID, entityID, action)

NotificationListView.onClickAction = new_onClickAction
NotificationPopUpViewer.onClickAction = new_onClickPopup

old_npuv_sendMessageForDisplay = NotificationPopUpViewer._NotificationPopUpViewer__sendMessageForDisplay

def new_npuv_sendMessageForDisplay(self, notification):
    if stat.config.get('showPopUp', True):
        old_npuv_sendMessageForDisplay(self, notification)

NotificationPopUpViewer._NotificationPopUpViewer__sendMessageForDisplay = new_npuv_sendMessageForDisplay

old_brf_format = BattleResultsFormatter.format

def showConfirmDialog(message, callback):
    DialogsInterface.showDialog(SimpleDialogMeta(title="Confirm", message=message, buttons=I18nConfirmDialogButtons()), callback)

def new_brf_format(self, message, *args):
    result = old_brf_format(self, message, *args)
    arenaUniqueID = message.data.get('arenaUniqueID', 0)
    stat.queue.put(arenaUniqueID)
    if stat.config.get('enableBattleEndedMessage', True) and hasattr(BigWorld.player(), 'arena'):
        if BigWorld.player().arena.arenaUniqueID != arenaUniqueID:
            isWinner = message.data.get('isWinner', 0)
            battleEndedMessage = ''
            if isWinner < 0:
                battleEndedMessage = stat.config.get('battleEndedMessageDefeat', '')
            elif isWinner > 0:
                battleEndedMessage = stat.config.get('battleEndedMessageWin', '')
            else:
                battleEndedMessage = stat.config.get('battleEndedMessageDraw', '')
            battleEndedMessage = battleEndedMessage.encode('utf-8')
            playerVehicles = message.data['playerVehicles'].itervalues().next()
            vehicleCompDesc = playerVehicles['vehTypeCompDescr']
            vt = vehiclesWG.getVehicleType(vehicleCompDesc)
            battleEndedMessage = battleEndedMessage.replace('{{vehicle-long}}', vt.userString)
            name = vt.name.replace(':', '-')
            battleEndedMessage = battleEndedMessage.replace('{{vehicle-raw}}', name)
            battleEndedMessage = battleEndedMessage.replace('{{vehicle-short}}', vt.shortUserString)
            arenaTypeID = message.data.get('arenaTypeID', 0)
            arenaType = ArenaType.g_cache[arenaTypeID]
            arenaName = i18n.makeString(arenaType.name)
            xp = message.data.get('xp', 0)
            credits = message.data.get('credits', 0)
            battleEndedMessage = battleEndedMessage.replace('{{map}}', arenaName)
            battleEndedMessage = battleEndedMessage.replace('{{map-raw}}', arenaType.geometryName)
            battleEndedMessage = battleEndedMessage.replace('{{xp}}', str(xp))
            battleEndedMessage = battleEndedMessage.replace('{{credits}}', str(credits))
            MessengerEntry.g_instance.gui.addClientMessage(battleEndedMessage)
    return result

BattleResultsFormatter.format = new_brf_format

stat = SessionStatistic()
