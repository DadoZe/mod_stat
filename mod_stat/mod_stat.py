# Embedded file name: mod_stat
import AccountCommands
import ArenaType
import BigWorld
import ResMgr
import codecs
import copy
import datetime
import json
import math
import os
import re
import threading
import urllib
import urllib2
from Account import Account
from PlayerEvents import g_playerEvents
from Queue import Queue
from account_helpers import BattleResultsCache
from adisp import async, process
from debug_utils import *
from gui import DialogsInterface
from gui import SystemMessages
from gui.Scaleform.daapi.view.dialogs import SimpleDialogMeta, I18nConfirmDialogButtons
from gui.battle_control.battle_session import BattleSessionProvider
from gui.shared import event_dispatcher
from gui.shared import g_eventBus, events
from gui.shared.gui_items.dossier import VehicleDossier
from gui.shared.gui_items.processors import makeSuccess
from gui.shared.gui_items.processors.common import BattleResultsGetter
from gui.shared.utils.requesters import StatsRequester
from helpers import dependency
from helpers import getClientLanguage
from helpers import i18n
from items import vehicles as vehiclesWG
from messenger import MessengerEntry
from messenger.proto.events import g_messengerEvents
from notification.NotificationListView import NotificationListView
from notification.NotificationPopUpViewer import NotificationPopUpViewer
from skeletons.gui.battle_results import IBattleResultsService
from skeletons.gui.battle_session import IBattleSessionProvider
from skeletons.gui.shared import IItemsCache
from xml.dom.minidom import parseString

g_itemsCache = dependency.instance(IItemsCache)

GENERAL = 0
BY_TANK = 1
VERSION = '0.9.19.0.2 beta'
URLLINK = 'http://bit.ly/YasenKrasen'

print 'Loading mod: YasenKrasen Session Statistics ' + VERSION + ' (http://forum.worldoftanks.eu/index.php?/topic/583433-)'

def MYPPRINT(obj, name = None):
    import inspect, pprint
    if isinstance(obj, dict) or isinstance(obj, list):
        pprint.pprint(obj)
    elif hasattr(obj, '__call__'):
        pprint.pprint(inspect.getargspec(obj))
    else:
        pprint.pprint(inspect.getmembers(obj))
    return

def hexToRgb(hex):
    return [ int(hex[i:i + 2], 16) for i in range(1, 6, 2) ]

def gradColor(startColor, endColor, val):
    start = hexToRgb(startColor)
    end = hexToRgb(endColor)
    grad = []
    for i in [0, 1, 2]:
        grad.append(start[i] * (1.0 - val) + end[i] * val)

    return '#%02x%02x%02x' % (grad[0], grad[1], grad[2])

stat = None

class SessionStatistic(object):

    def __init__(self):
        self.page = GENERAL
        self.cacheVersion = 10
        self.queue = Queue()
        self.loaded = False
        self.configIsValid = True
        self.battleStats = {}
        self.cache = {}
        self.account = {}
        self.session = {}
        self.impact = {}
        self.tanks = {}
        self.config = {}
        self.expectedValues = {}
        self.battles = []
        self.battleStatPatterns = []
        self.messageGeneral = ''
        self.messageByTank = ''
        self.panelByTank = ''
        self.messagePanel = ''
        self.playerName = ''
        self.bgIcon = ''
        self.startDate = None
        self.thousandSeparator = ' '
        self.useParametersPanel = False
        self.lastArenaUniqueID = None
        self.battleResultsAvailable = threading.Event()
        self.battleResultsAvailable.clear()
        self.battleResultsBusy = threading.Lock()
        self.thread = threading.Thread(target=self.mainLoop)
        self.thread.setDaemon(True)
        self.thread.start()

        path = '/'.join(['.', 'mods', 'configs', 'yk-stats'])
        if not os.path.exists(path):
            path = '/'.join(['.', 'res_mods', 'configs', 'yk-stats'])
        if os.path.isdir(path):
            self.configFilePath = '/'.join([path, 'config.json'])
            self.statCacheFilePath = '/'.join([path, 'cache.json'])
            self.expectedValuesPath = '/'.join([path, 'expected_tank_values.json'])
        self.readConfig()
        return

    def load(self):
        if self.loaded and self.playerName == BigWorld.player().name:
            return

        if not g_itemsCache.items.isSynced():
            LOG_NOTE('waiting for sync')
            # we need to be in sync to get account stats (probably)
            BigWorld.callback(1, stat.load)
            return

        self.loaded = True
        self.battles = []
        self.playerName = BigWorld.player().name

        if self.config.get('updateExpectedTankValues', True):
            expurl = self.config.get('urlForExpectedTankValues', 'http://www.wnefficiency.net/exp/expected_tank_values_latest.json')
            try:
                expfile = json.load(open(self.expectedValuesPath))
                verfile = json.dumps(expfile['header']['version'])
            except:
                verfile = ''
                LOG_NOTE('[mod_stat] No valid expected_tank_values.json found, trying ' + expurl + '.')

            try:
                expdata = json.load(urllib2.urlopen(expurl, timeout=3))
                verdata = json.dumps(expdata['header']['version'])
                if verfile != verdata:
                    urllib.urlretrieve(expurl, self.expectedValuesPath)
                    LOG_NOTE('[mod_stat] expected_tank_values.json updated to v' + verdata + '.')
                    SystemMessages.pushMessage("<font color='#BFE9FF'>Yasen</font><font color='#FF3333'>Krasen</font> Info!\n\nExpected Tank Values updated to v" + verdata + '.\n', type=SystemMessages.SM_TYPE.Warning)
            except:
                LOG_NOTE('[mod_stat] Unable to access ' + expurl + '.')

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
                try:
                    self.cache = json.load(jsonCache)
                    self.startDate = self.cache.get('date', self.getWorkDate())
                    if self.cache.get('version', 0) == self.cacheVersion and (self.startDate == self.getWorkDate() or not self.config.get('dailyAutoReset', True)) and not self.config.get('clientReloadReset', False):
                        if self.cache.get('players', {}).has_key(self.playerName):
                            playerCache = self.cache['players'][self.playerName]
                            self.battles = playerCache['battles']
                            self.account = playerCache['account']
                            self.session = playerCache['session']
                            self.impact = playerCache['impact']
                            self.tanks = playerCache['tanks']
                        invalidCache = False
                except:
                    LOG_NOTE('[mod_stat] Unable to read player''s cache.')
        if invalidCache:
            self.reset()
        else:
            self.updateMessage()

        if self.config.get('checkForUpdate', True):
            try:
                file = urllib2.urlopen('https://pastebin.com/raw/MNWpVKbL')
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
                        SystemMessages.pushMessage("<font color='#BFE9FF'>Yasen</font><font color='#FF3333'>Krasen</font> Info!\n\n" + infoMessage + '\n', type=SystemMessages.SM_TYPE.GameGreeting)
            except:
                LOG_NOTE('[mod_stat] Unable to access remote update file.')

    def readConfig(self):
        with codecs.open(self.configFilePath, 'r', 'utf-8-sig') as configFileJson:
            try:
                self.config = json.load(configFileJson)
                self.config.update(self.config.get(getClientLanguage(), self.config.get("en", {})))
                self.battleStatPatterns = []
                for pattern in self.config.get('battleStatPatterns', []):
                    try:
                        condition = pattern.get('if', 'True')
                        condition = re.sub('{{(\\w+)}}', "values['\\1']", condition)
                    except:
                        LOG_NOTE('[mod_stat] Invalid condition ' + pattern.get('if', ''))
                        continue

                    try:
                        compiled = re.compile(pattern.get('pattern', ''))
                        self.battleStatPatterns.append({'condition': condition, 'pattern': compiled, 'repl': pattern.get('repl', '')})
                    except:
                        LOG_NOTE('[mod_stat] Invalid pattern ' + pattern.get('pattern', ''))
                        continue

                self.thousandSeparator = self.config.get('thousandSeparator', ' ')
                self.useMessenger = self.config.get('useMessenger', True)
                self.enableByTank = self.config.get('enableByTank', True)
                self.useParametersPanel = self.config.get('useParametersPanel', False)
                self.enablePanelAccount = self.config.get('enablePanelAccount', False)
                self.enablePanelSession = self.config.get('enablePanelSession', False)
                self.enablePanelImpact = self.config.get('enablePanelImpact', False)
                self.enableByTankPanel = self.config.get('enableByTankPanel', False)
                self.enableResearchWatchdog = self.config.get('enableResearchWatchdog', False)
                setHandlers(self)
                self.configIsValid = True
            except:
                LOG_CURRENT_EXCEPTION()
                LOG_NOTE('[mod_stat] load config.json has failed')
                self.config = {}
                self.configIsValid = False

    def getWorkDate(self):
        if datetime.datetime.now().hour >= self.config.get('dailyAutoResetHour', 4):
            return datetime.date.today().strftime('%Y-%m-%d')
        return (datetime.date.today() - datetime.timedelta(days=1)).strftime('%Y-%m-%d')

    def save(self):
        if self.account and self.session:
            self.impact = self.calcWN8([self.account['values'], self.session['values']], fromBattleResult=False, forTank=False)
            self.impact['_type'] = 'impact'

        statCache = open(self.statCacheFilePath, 'w')
        self.cache['version'] = self.cacheVersion
        self.cache['date'] = self.startDate
        if not self.cache.has_key('players'):
            self.cache['players'] = {}
        fastCache = self.config.get("fastCache", False)
        self.cache['players'][self.playerName] = {
          'battles': [] if fastCache else self.battles,
          'account': self.account,
          'session': self.session,
          'impact': self.impact,
          'tanks': self.tanks
        }
        if fastCache:
            statCache.write(json.dumps(self.cache))
        else:
            statCache.write(json.dumps(self.cache, sort_keys=True, indent=4, separators=(',', ': ')))
        statCache.close()

    def createMessage(self):
        msg = {GENERAL: self.messageGeneral, BY_TANK: self.messageByTank}[self.page]
        message = {
         'typeID': 1,
         'message': {'bgIcon': self.bgIcon,
                     'defaultIcon': '',
                     'savedData': 0,
                     'timestamp': -1,
                     'filters': [],
                     'buttonsLayout': [],
                     'message': msg,
                     'type': 'black',
                     'icon': self.config.get('icon', '')},
         'entityID': 99999,
         'auxData': ['GameGreeting']}
        return message

    def mainLoop(self):
        while True:
            self.battleResultsBusy.acquire()
            arenaUniqueID, callWhenDone = self.queue.get()
            LOG_NOTE('got arenaUniqueID from the queue start %s' % str(arenaUniqueID))
            self.battleResultsAvailable.wait()
            BigWorld.player().battleResultsCache.get(arenaUniqueID, lambda resID, value: self.battleResultsCallback(arenaUniqueID, resID, value, callWhenDone))
            LOG_NOTE('got arenaUniqueID from the queue end %s' % str(arenaUniqueID))

    def battleResultsCallback(self, arenaUniqueID, responseCode, value = None, callWhenDone = None):
        LOG_NOTE('battleResultsCallback start %s' % str(arenaUniqueID))
        #RES_FAILURE = -1
        #RES_WRONG_ARGS = -2
        #RES_NON_PLAYER = -3
        #RES_SHOP_DESYNC = -4
        #RES_COOLDOWN = -5
        #RES_HIDDEN_DOSSIER = -6
        #RES_CENTER_DISCONNECTED = -7
        #RES_TUTORIAL_DISABLED = -8
        #RES_NOT_AVAILABLE = -10
        #RES_SUCCESS = 0
        #RES_STREAM = 1
        #RES_CACHE = 2
        if responseCode == AccountCommands.RES_NON_PLAYER or responseCode == AccountCommands.RES_COOLDOWN:
            self.queue.put((arenaUniqueID, callWhenDone))
            BigWorld.callback(1.0, lambda: self.battleResultsBusy.release())
            LOG_NOTE('battleResultsCallback end %s %s' % (str(arenaUniqueID), str(responseCode)))
            return
        if responseCode < 0:
            self.battleResultsBusy.release()
            LOG_NOTE('battleResultsCallback end %s %s' % (str(arenaUniqueID), str(responseCode)))
            return
        try:
            lastArenaUniqueID = None
            if self.lastArenaUniqueID==arenaUniqueID:
                self.lastArenaUniqueID = None
                lastArenaUniqueID = arenaUniqueID
            isSuccess = True
            if arenaUniqueID in self.battleStats:
                LOG_NOTE('We have processed this arenaUniqueID already!')
                isSuccess = False
            else:
                self.processBattleResults(value)
                BigWorld.callback(0, lambda: dependency.instance(IBattleResultsService).postResult(value, self.config.get('showEachBattleResultsWindow', False) or lastArenaUniqueID==arenaUniqueID))
        except:
            LOG_CURRENT_EXCEPTION()
        finally:
            LOG_NOTE('finally')
            self.battleResultsBusy.release()
            if isSuccess and callWhenDone:
                BigWorld.callback(0, callWhenDone)
            LOG_NOTE('battleResultsCallback end %s' % str(arenaUniqueID))

    def processBattleResults(self, value):
        LOG_NOTE('processBattleResults start')
        try:
            arenaUniqueID = value['arenaUniqueID']
            arenaTypeID = value['common']['arenaTypeID']
            arenaType = ArenaType.g_cache[arenaTypeID]
            personal = value['personal'].itervalues().next()
            idNum = personal['typeCompDescr']
            arenaName = i18n.makeString(arenaType.name)
            vt = vehiclesWG.getVehicleType(idNum)
            result = 1 if int(personal['team']) == int(value['common']['winnerTeam']) else (0 if not int(value['common']['winnerTeam']) else -1)
            death = 1 if int(personal['deathReason']) > -1 else 0
            teamResources = 0
            teamInfluencePoints = 0
            if personal['fortResource'] is None:
                fortResource = 0
            else:
                fortResource = int(personal['fortResource'])
            if personal['influencePoints'] is None:
                influencePoints = 0
            else:
                influencePoints = int(personal['influencePoints'])
            place = 1
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
                if personal['team'] == vehicle[0]['team']:
                    teamResources += vehicle[0]['fortResource']
                    teamInfluencePoints += vehicle[0]['influencePoints']

            battleTier = 11 if max(squadsTier.values()) == 10 and min(squadsTier.values()) == 9 else max(squadsTier.values())
            proceeds = personal['credits'] - personal['autoRepairCost'] - personal['autoEquipCost'][0] - personal['autoLoadCost'][0]
            tmenXP = personal['tmenXP']
            if 'premium' in vt.tags:
                tmenXP = int(1.5 * tmenXP)
            battle = {
             'idNum': idNum,
             'vehicle': vt.name.replace(':', '-'),
             'tier': vt.level,
             'result': result,
             'dailyXPFactor': personal['dailyXPFactor10'] / 10,
             'gametype': value['common']['guiType'],
             'damage': personal['damageDealt'],
             'damageRec': personal['damageReceived'],
             'potDamageRec': personal['potentialDamageReceived'],
             'deathsCount': death,
             'frag': personal['kills'],
             'fortResource': fortResource,
             'teamResources': teamResources,
             'influencePoints': influencePoints,
             'teamInfluencePoints': teamInfluencePoints,
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
             'grossGold': personal['gold'],
             'netGold': personal['gold'] - personal['autoEquipCost'][1] - personal['autoLoadCost'][1],
             'battleTier': battleTier,
             'damageAssistedRadio': personal['damageAssistedRadio'],
             'damageAssistedTrack': personal['damageAssistedTrack'],
             'assist': personal['damageAssistedRadio'] + personal['damageAssistedTrack'],
             'vehicle-raw': vt.name.replace(':', '-'),
             'vehicle-short': vt.shortUserString,
             'vehicle-long': vt.userString,
             'map-raw': arenaType.geometryName,
             'map': arenaName,
             'result': result,
             'autoRepair': personal['autoRepairCost'],
             'autoEquip': personal['autoEquipCost'][0],
             'autoLoad': personal['autoLoadCost'][0]
            }
            battleStat = self.calcWN8([battle])

            self.battleStats[arenaUniqueID] = battleStat

            if self.config.get('dailyAutoReset', True) and self.startDate != stat.getWorkDate():
                self.reset()

            if value['common']['guiType'] in self.config.get('battleType', [1]):
                self.battles.append(battle)

                last_values = None

                if self.session:
                    self.session = self.calcWN8([self.session['values'], battleStat['values']], fromBattleResult=False, forTank=False)
                else:
                    self.session = copy.deepcopy(battleStat)
                self.session['_type'] = 'session'

                idNum = str(idNum) #tanks restored from cache will have this key as string
                if idNum in self.tanks:
                    self.tanks[idNum] = self.calcWN8([self.tanks[idNum]['values'], battleStat['values']], fromBattleResult=False)
                else:
                    self.tanks[idNum] = copy.deepcopy(battleStat)
                self.tanks[idNum]['_type'] = 'tanks'
            self.updateMessage()
            self.save()
        except:
            LOG_CURRENT_EXCEPTION()
        finally:
            LOG_NOTE('processBattleResults end')

    def reset(self):
        LOG_NOTE('reset start')
        self.page = GENERAL
        self.startDate = self.getWorkDate()
        self.battles = []
        self.account = {}
        self.session = {}
        self.impact = {}
        self.tanks = {}
        self.getAccountStats()
        self.updateMessage()
        LOG_NOTE('reset end')

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

        val = tierExpected.copy()
        self.expectedValues[newIdNum] = val
        return val

    def xeff(self, x):
        if x > 2300:
            return 100
        return int(max(0, min(100, x * (x * (x * (x * (x * (x * 6.449e-18 - 4.089e-14) + 8.302e-11) - 4.433e-08) - 4.82e-05) + 0.1257) - 40.42)))

    def xwn8(self, x):
        if x > 3800:
            return 100
        return int(max(0, min(100, x * (x * (x * (x * (x * (-x * 9.762e-20 + 1.6221e-15) - 1.007e-11) + 2.7916e-08) - 3.6982e-05) + 0.05577) - 1.3)))

    def calcWN8(self, battles, fromBattleResult = True, forTank = True):
        values = {}
        values['battlesCount'] = 1 if fromBattleResult else 0
        totalTier = 0
        totalPlace = 0
        medPlace = 0
        places = []
        totalBattleTier = 0
        valuesKeys = ['winsCount',
         'defeatsCount',
         'drawsCount',
         'dailyXPFactor',
         'totalDmg',
         'totalDmgRec',
         'totalMileage',
         'totalMileagekm',
         'totalPotDmgRec',
         'totalDeathsCount',
         'totalFrag',
         'totalShots',
         'totalHits',
         'totalPierced',
         'totalSpot',
         'totalDef',
         'totalCap',
         'totalAssist',
         'totalDmgAssistTrack',
         'totalDmgAssistRadio',
         'totalXP',
         'allXP',
         'totalOriginXP',
         'totalFreeXP',
         'totalOriginalFreeXP',
         'totalOriginPremXP',
         'totalTmenXP',
         'totalEventTmenXP',
         'totalResources',
         'totalTeamResources',
         'totalInfluence',
         'totalTeamInfluence',
         'autoRepairCost',
         'autoLoadCost',
         'autoEquipCost',
         'service',
         'grossCredits',
         'netCredits',
         'grossGold',
         'netGold',
         'autoRepairGBMCost',
         'autoLoadGBMCost',
         'autoEquipGBMCost',
         'place',
         'battlesCountSpecial',
         'battlesCountRandom',
         'battlesCountTraining',
         'battlesCountCompany',
         'battlesCountTutorial',
         'battlesCountTeam',
         'battlesCountFallout',
         'battlesCountEvents',
         'battlesCountStrongholdSkirmishOld',
         'battlesCountStronghold',
         'battlesCountRatedTeam',
         'battlesCountRatedSandbox',
         'battlesCountSandbox',
         'battlesCountFalloutClassic',
         'battlesCountFalloutMultiteam',
         'battlesCountStrongholdSkirmish',
         'battlesCountStrongholdAdvances',
         'battlesCountRanked']
        for key in valuesKeys:
            values[key] = 0

        expKeys = ['expDamage', 'expFrag', 'expSpot', 'expDef', 'expWinRate']
        #expValues = {}
        for key in expKeys:
            #expValues['total_' + key] = 0.0
            values['total_' + key] = 0.0

        resCounters = {-1: 'defeatsCount',
         0: 'drawsCount',
         1: 'winsCount'}
        battleCounters = {0: 'battlesCountSpecial',
         1: 'battlesCountRandom',
         2: 'battlesCountTraining',
         3: 'battlesCountCompany',
         4: 'battlesCountTutorial',
         5: 'battlesCountTeam',
         6: 'battlesCountFallout',
         7: 'battlesCountEvents',
         8: 'battlesCountStrongholdSkirmishOld',
         9: 'battlesCountStronghold',
         10: 'battlesCountRatedTeam',
         11: 'battlesCountRatedSandbox',
         12: 'battlesCountSandbox',
         13: 'battlesCountFalloutClassic',
         14: 'battlesCountFalloutMultiteam',
         15: 'battlesCountStrongholdSkirmish',
         16: 'battlesCountStrongholdAdvances',
         17: 'battlesCountRanked'}
        for battle in battles:
            battlesCount = 1
            if fromBattleResult:
                values[resCounters[battle['result']]] += 1
                values[battleCounters[battle['gametype']]] += 1
                values['totalDmg'] += battle['damage']
                values['totalDmgRec'] += battle['damageRec']
                values['totalPotDmgRec'] += battle['potDamageRec']
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
                values['totalXP'] += battle['xp']
                values['allXP'] += battle['xp'] + battle['freeXP']
                values['totalOriginXP'] += battle['originalXP']
                values['totalOriginPremXP'] += int(battle['originalPremXP'])
                values['totalFreeXP'] += battle['freeXP']
                values['totalOriginalFreeXP'] += battle['originalFreeXP']
                values['totalTmenXP'] += battle['tmenXP']
                values['totalEventTmenXP'] += battle['eventTmenXP']
                values['totalResources'] += battle['fortResource']
                values['totalTeamResources'] += battle['teamResources']
                values['totalInfluence'] += battle['influencePoints']
                values['totalTeamInfluence'] += battle['teamInfluencePoints']
                values['totalMileage'] += battle['mileage']
                values['totalMileagekm'] += battle['mileage'] / float(1000)
                values['autoRepairCost'] = battle['autoRepairCost']
                values['autoLoadCost'] = battle['autoLoadCost']
                values['autoEquipCost'] = battle['autoEquipCost']
                values['autoRepairGBMCost'] = battle['autoRepairCost']
                values['autoLoadGBMCost'] = battle['autoLoadCost']
                values['autoEquipGBMCost'] = battle['autoEquipCost']
                values['service'] += battle['service']
                values['netCredits'] += battle['netCredits']
                values['grossCredits'] += battle['grossCredits']
                values['grossGold'] += battle['grossGold']
                values['netGold'] += battle['netGold']
                values['place'] = battle['place']
                values['dailyXPFactor'] = battle['dailyXPFactor']
                totalTier += battle['tier']
                totalBattleTier += battle['battleTier']
                totalPlace += battle['place']
                places.append(battle['place'])
            else:
                battlesCount = battle['battlesCount']
                if 'losses' in battle: # vehicle stats from account info
                    values['battlesCount'] += battlesCount
                    values['defeatsCount'] += battle['losses']
                    values['drawsCount'] += (battlesCount-battle['losses']-battle['wins'])
                    values['winsCount'] += battle['wins']
                    values['battlesCountRandom'] += battlesCount
                    values['totalDmg'] += battle['damageDealt']
                    values['totalDmgRec'] += battle['damageReceived']
                    values['totalPotDmgRec'] += battle['potentialDamageReceived']
                    values['totalDeathsCount'] += (battlesCount-battle['survivedBattles'])
                    values['totalFrag'] += battle['frags']
                    values['totalSpot'] += battle['spotted']
                    values['totalDef'] += battle['droppedCapturePoints']
                    values['totalCap'] += battle['capturePoints']
                    values['totalShots'] += battle['shots']
                    values['totalHits'] += battle['directHits']
                    values['totalPierced'] += battle['piercings']
                    values['totalAssist'] += (battle['damageAssistedRadio']+battle['damageAssistedTrack'])
                    values['totalDmgAssistTrack'] += battle['damageAssistedTrack']
                    values['totalDmgAssistRadio'] += battle['damageAssistedRadio']
                    values['totalXP'] += battle['xp']
                    #...
                    totalTier += (battlesCount*battle['tier'])
                    totalBattleTier += (battlesCount*battle['tier'])
                    totalPlace += 0
                    places.append(0)
                else:
                    for key in ['battlesCount', 'defeatsCount', 'drawsCount', 'winsCount', 'battlesCountRandom', \
                                'totalDmg', 'totalDmgRec', 'totalPotDmgRec', 'totalDeathsCount', 'totalFrag', 'totalSpot', 'totalDef', \
                                'totalCap', 'totalShots', 'totalHits', 'totalPierced', 'totalAssist', 'totalDmgAssistTrack', \
                                'totalDmgAssistRadio', 'totalXP', 'allXP', 'totalOriginXP', 'totalOriginPremXP', 'totalFreeXP', \
                                'totalOriginalFreeXP', 'totalTmenXP', 'totalEventTmenXP', 'totalResources', 'totalTeamResources', \
                                'totalInfluence', 'totalTeamInfluence', 'totalMileage', 'totalMileagekm', 'autoRepairCost', \
                                'autoLoadCost', 'autoEquipCost', 'autoRepairGBMCost', 'autoLoadGBMCost', 'autoEquipGBMCost', \
                                'service', 'netCredits', 'grossCredits', 'grossGold', 'netGold', 'place', 'dailyXPFactor']:
                        values[key] += battle[key]
                    totalTier += (battlesCount*battle['avgTier'])
                    totalBattleTier += (battlesCount*battle['avgBattleTier'])
                    totalPlace += (battlesCount*battle['avgPlace'])
                    medPlace += (battlesCount*battle['medPlace'])

            if forTank: #'idNum' in battle:
                idNum = battle['idNum']
                if not self.expectedValues.has_key(idNum):
                    val = self.calcExpected(idNum)
                val = self.expectedValues[idNum]
                for key in expKeys:
                    values['total_' + key] += (val[key]*battlesCount)
                for key in ['idNum', 'vehicle-raw', 'vehicle-short', 'vehicle-long']:
                    values[key] = battle[key]
            else:
                for key in expKeys:
                    values['total_' + key] += battle['total_' + key]

        if values['battlesCount'] > 0:
            values['avgWinRate'] = float(values['winsCount']) / values['battlesCount'] * 100
            values['avgDamage'] = float(values['totalDmg']) / values['battlesCount']
            values['avgDamageRec'] = int(values['totalDmgRec'] / values['battlesCount'])
            values['avgPotDmgRec'] = int(values['totalPotDmgRec'] / values['battlesCount'])
            values['avgDeathsCount'] = 0 if values['totalDeathsCount'] < 1 else float(values['totalDeathsCount']) / values['battlesCount']
            values['avgFrag'] = float(values['totalFrag']) / values['battlesCount']
            values['avgShots'] = float(values['totalShots']) / values['battlesCount']
            values['hitsRate'] = 0 if values['totalShots'] < 1 else float(values['totalHits']) / values['totalShots'] * 100
            values['deathsRate'] = 0 if values['totalDeathsCount'] < 1 else float(values['totalDeathsCount']) / values['battlesCount'] * 100
            values['survivalRate'] = 100 if values['totalDeathsCount'] < 1 else abs(float(values['totalDeathsCount']) / values['battlesCount'] * 100 - 100)
            values['effHitsRate'] = 0 if values['totalHits'] < 1 else float(values['totalPierced']) / values['totalHits'] * 100
            values['avgMileage'] = float(values['totalMileage']) / values['battlesCount']
            values['avgMileagekm'] = float(values['totalMileage'] / values['battlesCount']) / 1000
            values['avgSpot'] = float(values['totalSpot']) / values['battlesCount']
            values['avgDef'] = float(values['totalDef']) / values['battlesCount']
            values['avgCap'] = float(values['totalCap']) / values['battlesCount']
            values['avgAssist'] = int(values['totalAssist']) / values['battlesCount']
            values['avgDmgAssistTrack'] = int(values['totalDmgAssistTrack']) / values['battlesCount']
            values['avgDmgAssistRadio'] = int(values['totalDmgAssistRadio']) / values['battlesCount']
            values['avgXP'] = int(values['totalXP'] / values['battlesCount'])
            values['avgOriginalXP'] = int(values['totalOriginXP'] / values['battlesCount'])
            values['avgOriginalPremXP'] = int(values['totalOriginPremXP'] / values['battlesCount'])
            values['avgFreeXP'] = int(values['totalFreeXP'] / values['battlesCount'])
            values['avgOriginalFreeXP'] = int(values['totalOriginalFreeXP'] / values['battlesCount'])
            values['avgTmenXP'] = int(values['totalTmenXP'] / values['battlesCount'])
            values['avgEventTmenXP'] = int(values['totalEventTmenXP'] / values['battlesCount'])
            values['avgNetCredits'] = int(values['netCredits'] / values['battlesCount'])
            values['avgGrossCredits'] = int(values['grossCredits'] / values['battlesCount'])
            values['avgService'] = int(values['service'] / values['battlesCount'])
            values['avgTier'] = float(totalTier) / values['battlesCount']
            values['avgBattleTier'] = float(totalBattleTier) / values['battlesCount']
            values['avgPlace'] = round(float(totalPlace) / values['battlesCount'], 1)
            if 'battlesCountStrongholdSkirmish' in values and values['battlesCountStrongholdSkirmish'] > 0:
                values['avgResources'] = int(values['totalResources'] / values['battlesCountStrongholdSkirmish'])
                values['avgTeamResources'] = int(values['totalTeamResources'] / values['battlesCountStrongholdSkirmish'])
                values['avgInfluence'] = int(values['totalInfluence'] / values['battlesCountStrongholdSkirmish'])
                values['avgTeamInfluence'] = int(values['totalTeamInfluence'] / values['battlesCountStrongholdSkirmish'])
            else:
                values['avgResources'] = 0
                values['avgTeamResources'] = 0
                values['avgInfluence'] = 0
                values['avgTeamInfluence'] = 0

            if fromBattleResult:
                places = sorted(places)
                length = len(places)
                values['medPlace'] = (places[length / 2] + places[length / 2 - 1]) / 2.0 if not length % 2 else float(places[length / 2])
            else:
                values['medPlace'] = round(float(medPlace) / values['battlesCount'], 1)

            for key in expKeys:
                values[key] = values['total_' + key] / values['battlesCount']

            #values['WN6'] = max(0, int((1240 - 1040 / min(values['avgTier'], 6) ** 0.164) * values['avgFrag'] + values['avgDamage'] * 530 / (184 * math.exp(0.24 * values['avgTier']) + 130) + values['avgSpot'] * 125 + min(values['avgDef'], 2.2) * 100 + (185 / (0.17 + math.exp((values['avgWinRate'] - 35) * -0.134)) - 500) * 0.45 + (6 - min(values['avgTier'], 6)) * -60))
            #values['XWN6'] = 100 if values['WN6'] > 2300 else int(max(min(values['WN6'] * (values['WN6'] * (values['WN6'] * (values['WN6'] * (values['WN6'] * (4.66e-18 * values['WN6'] - 3.2413e-14) + 7.524e-11) - 6.516e-08) + 1.307e-05) + 0.05153) - 3.9, 100), 0))
            #values['WN7'] = max(0, int((1240 - 1040 / min(values['avgTier'], 6) ** 0.164) * values['avgFrag'] + values['avgDamage'] * 530 / (184 * math.exp(0.24 * values['avgTier']) + 130) + values['avgSpot'] * 125 * min(values['avgTier'], 3) / 3 + min(values['avgDef'], 2.2) * 100 + (185 / (0.17 + math.exp((values['avgWinRate'] - 35) * -0.134)) - 500) * 0.45 - (5 - min(values['avgTier'], 5)) * 125 / (1 + math.exp((values['avgTier'] - (values['battlesCount'] / 220) ** (3 / values['avgTier'])) * 1.5))))
            #values['XWN7'] = 100 if values['WN7'] > 2315 else int(max(min(values['WN7'] * (values['WN7'] * (values['WN7'] * (values['WN7'] * (values['WN7'] * (4.359e-18 * values['WN7'] - 3.262e-14) + 8.6287e-11) - 1.0299e-07) + 6.373e-05) + 0.02439) - 0.58, 100), 0))
            values['EFF'] = max(0, values['avgDamage'] * (10 / (values['avgTier'] + 2)) * (0.23 + 2 * values['avgTier'] / 100) + values['avgFrag'] * 250 + values['avgSpot'] * 150 + math.log(values['avgCap'] + 1, 1.732) * 150 + values['avgDef'] * 150)
            values['XEFF'] = self.xeff(values['EFF'])
            values['BR'] = max(0, int(values['avgDamage'] * (0.2 + 1.5 / values['avgTier']) + values['avgFrag'] * (350 - values['avgTier'] * 20) + values['avgDmgAssistRadio'] / 2 * (0.2 + 1.5 / values['avgTier']) + values['avgDmgAssistTrack'] / 2 * (0.2 + 1.5 / values['avgTier']) + values['avgSpot'] * 200 + values['avgCap'] * 15 + values['avgDef'] * 15))
        else:
            for key in ['avgResources',
             'avgTeamResources',
             'avgInfluence',
             'avgTeamInfluence',
             'avgWinRate',
             'avgDamage',
             'avgDamageRec',
             'avgMileage',
             'avgMileagekm',
             'avgPotDmgRec',
             'survivalRate',
             'deathsRate',
             'avgDeathsCount',
             'avgFrag',
             'avgShots',
             'hitsRate',
             'effHitsRate',
             'avgSpot',
             'avgDef',
             'avgCap',
             'avgAssist',
             'avgDmgAssistTrack',
             'avgDmgAssistRadio',
             'avgXP',
             'avgOriginalXP',
             'avgOriginalPremXP',
             'avgFreeXP',
             'avgOriginalFreeXP',
             'avgTmenXP',
             'avgEventTmenXP',
             'avgNetCredits',
             'avgGrossCredits',
             'avgService',
             'avgTier',
             'avgBattleTier',
             'medPlace',
             'avgPlace',
             'WN6',
             'XWN6',
             'WN7',
             'XWN7',
             'EFF',
             'XEFF',
             'BR']:
                values[key] = 0

            for key in expKeys:
                values[key] = 1

        values['avgBattleTierDiff'] = values['avgBattleTier'] - values['avgTier']
        values['rDAMAGE'] = values['avgDamage'] / values['expDamage']
        values['rSPOT'] = values['avgSpot'] / values['expSpot']
        values['rFRAG'] = values['avgFrag'] / values['expFrag']
        values['rDEF'] = values['avgDef'] / values['expDef']
        values['rWIN'] = values['avgWinRate'] / values['expWinRate']
        values['rWINc'] = max(0, (values['rWIN'] - 0.71) / 0.29000000000000004)
        values['rDAMAGEc'] = max(0, (values['rDAMAGE'] - 0.22) / 0.78)
        values['rFRAGc'] = max(0, min(values['rDAMAGEc'] + 0.2, (values['rFRAG'] - 0.12) / 0.88))
        values['rSPOTc'] = max(0, min(values['rDAMAGEc'] + 0.1, (values['rSPOT'] - 0.38) / 0.62))
        values['rDEFc'] = max(0, min(values['rDAMAGEc'] + 0.1, (values['rDEF'] - 0.1) / 0.9))
        values['WN8'] = 980.0 * values['rDAMAGEc'] + 210.0 * values['rDAMAGEc'] * values['rFRAGc'] + 155.0 * values['rFRAGc'] * values['rSPOTc'] + 75.0 * values['rDEFc'] * values['rFRAGc'] + 145.0 * min(1.8, values['rWINc'])
        values['XWN8'] = self.xwn8(values['WN8'])
        values['avgDamage'] = int(values['avgDamage'])
        values['avgMileage'] = int(values['avgMileage'])

        if battles and 'EFF' in battles[0]:
            for key in ['avgWinRate', 'EFF', 'WN8']:
                values['d' + key] = values[key] - battles[0][key]

        gradient, palette = self.refreshColorMacros(values)
        return {'values': values, 'gradient': gradient, 'palette': palette}

    def applyMacros(self, val, prec = 2, sign = ''):
        if type(val) in [str, unicode]:
            return val
        if prec <= 0:
            sVal = format(int(round(val)), '%s,d' % sign)
        else:
            sVal = format(val, '%s,.%sf' % (sign, prec)) if type(val) is float else format(val, ',d')
        sVal = sVal.replace(',', self.thousandSeparator)
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

    def formatString(self, text, stats, not_found_replacement = None):
        #try:
        values = stats['values']
        for m in re.finditer("{{([gc]:)?([^}:]*)((:d)|(:1f)|:(\d+)|:(\d+)\.(\d+)f|(:\+d)|(:\+1f))?}}", text):
            g, g1, key, g2, sg1, sg2, sg3, sg4a, sg4b, sg5, sg6 = m.group(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
            if not key in values:
                if not_found_replacement is None:
                    LOG_NOTE('No key in values of %s (%s)' % (stats.get('_type', 'unknown'), key))
                else:
                    text = text.replace('%s' % g, not_found_replacement)
            elif g1 is None:
                if g2 is None:
                    text = text.replace('{{%s}}' % key, self.applyMacros(values[key]))
                elif sg1:
                    text = text.replace('{{%s:d}}' % key, self.applyMacros(values[key], 0))
                elif sg2:
                    text = text.replace('{{%s:1f}}' % key, self.applyMacros(values[key], 1))
                elif sg3:
                    xx = int(sg3)
                    text = text.replace('{{%s:%d}}' % (key, xx), self.applyMacros2(values[key], xx))
                elif sg4a:
                    xx, yy = int(sg4a), int(sg4b)
                    text = text.replace('{{%s:%d.%df}}' % (key, xx, yy), self.applyMacros2(values[key], xx, yy))
                elif sg5:
                    text = text.replace('{{%s:+d}}' % key, self.applyMacros(values[key], 0, '+'))
                elif sg6:
                    text = text.replace('{{%s:+1f}}' % key, self.applyMacros(values[key], 1, '+'))
            elif g1=="g:":
                text = text.replace('{{g:%s}}' % key, stats['gradient'][key])
            elif g1=="c:":
                text = text.replace('{{c:%s}}' % key, stats['palette'][key])
        #except:
        #  LOG_CURRENT_EXCEPTION()
        #finally:
        return text

    def updateMessage(self):
        LOG_NOTE('updateMessage start')
        if not self.configIsValid:
            self.messagePanel = "Session statistics' config.json is not valid"
            self.messageGeneral = "Session statistics' config.json is not valid"
            return
        try:

            if self.useParametersPanel:

                fullMsg = ''

                templateAccount = self.config.get('templatePanelAccount', '')
                if self.account and templateAccount and not self.session and self.enablePanelAccount:
                    msg = '\n'.join(templateAccount)
                    userMacros = self.config.get('userMacros', {})
                    for key in userMacros.keys():
                        msg = msg.replace('{{%s}}' % key, userMacros[key])
                    fullMsg = self.formatString(msg, self.account)

                if self.session and self.enablePanelSession:
                    if self.account and templateAccount and not self.session:
                        fullMsg = fullMsg + '\n\n'
                    bg = self.config.get('statBackground', '')
                    self.bgIcon = self.formatString(bg, self.session)
                    msg = '\n'.join(self.config.get('templatePanelSession', ''))
                    userMacros = self.config.get('userMacros', {})
                    for key in userMacros.keys():
                        msg = msg.replace('{{%s}}' % key, userMacros[key])
                    fullMsg = fullMsg + self.formatString(msg, self.session)

                    templateImpact = self.config.get('templatePanelImpact', '')
                    if self.impact and templateImpact and self.enablePanelImpact:
                        msg = '\n'.join(templateImpact)
                        userMacros = self.config.get('userMacros', {})
                        for key in userMacros.keys():
                            msg = msg.replace('{{%s}}' % key, userMacros[key])
                        fullMsg = fullMsg + '\n\n' + self.formatString(msg, self.impact)

                self.messagePanel = fullMsg

                if self.tanks and self.enableByTankPanel:
                    msg = self.config.get('byTankTitlePanel', '')
                    row = self.config.get('byTankStatsPanel', '')
                    sorting = self.config.get('sortReverse', True)
                    tankMacro = self.config.get('sortMacro', 'WN8')

                    for idNum in sorted(self.tanks.keys(), key=lambda value: self.tanks[value]['values'][tankMacro], reverse=sorting):
                        msg += '\n' + self.formatString(row, self.tanks[idNum])

                    userMacros = self.config.get('userMacros', {})
                    for key in userMacros.keys():
                        msg = msg.replace('{{%s}}' % key, userMacros[key])

                    self.panelByTank = msg
                else:
                    self.panelByTank = ''

                if self.useParametersPanel:
                    refreshPanelDisplay()

            if self.useMessenger:
                msg = '\n'.join(self.config.get('template', ''))
                userMacros = self.config.get('userMacros', {})
                for key in userMacros.keys():
                    msg = msg.replace('{{%s}}' % key, userMacros[key])
                bg = self.config.get('statBackground', '')
                msg = msg.replace('{{buttonGeneral}}', '<a href="event:yk-stat:buttonGeneral">' + self.config.get('buttonGeneral', 'General') + '</a>')
                msg = msg.replace('{{buttonTank}}', '<a href="event:yk-stat:buttonTank">' + self.config.get('buttonTank', 'by Tank') + '</a>')
                msg = msg.replace('{{buttonReset}}', '<a href="event:yk-stat:buttonReset">' + self.config.get('buttonReset', 'Reset') + '</a>')
                if self.session:
                    self.bgIcon = self.formatString(bg, self.session)
                    self.messageGeneral = self.formatString(msg, self.session)
                else:
                    self.bgIcon = self.formatString(bg, self.calcWN8([], False, False))
                    self.messageGeneral = self.formatString(msg, {'values': {}}, '0')

                if self.tanks and self.enableByTank:
                    msg = self.config.get('byTankTitle', '')
                    row = self.config.get('byTankStats', '')
                    sorting = self.config.get('sortReverse', True)
                    tankMacro = self.config.get('sortMacro', 'WN8')

                    for idNum in sorted(self.tanks.keys(), key=lambda value: self.tanks[value]['values'][tankMacro], reverse=sorting):
                        msg += '\n' + self.formatString(row, self.tanks[idNum])

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

        except:
            LOG_CURRENT_EXCEPTION()
        finally:
            LOG_NOTE('updateMessage end')

    def replaceBattleResultMessage(self, item, arenaUniqueID):
        if arenaUniqueID in self.battleStats:
            message = unicode(item['message'], 'utf-8')
            if self.config.get('debugBattleResultMessage', False):
                LOG_NOTE(message)
            stats = self.battleStats[arenaUniqueID]
            values = stats['values']
            for pattern in self.battleStatPatterns:
                try:
                    if not eval(pattern.get('condition')):
                        continue
                except:
                    LOG_NOTE('[mod_stat] Invalid calculation condition ' + pattern.get('condition'))
                    continue

                message = re.sub(pattern.get('pattern', ''), pattern.get('repl', ''), message)

            battleStatText = ''.join(self.config.get('battleStatText', ''))

            userMacros = self.config.get('userMacros', {})
            for key in userMacros.keys():
                if key in ('dailyXP',) and values[key + 'Factor'] == 1:
                    battleStatText = battleStatText.replace('{{%s}}' % key, '')
                if key in ('autoRepair', 'autoLoad', 'autoEquip', 'autoRepairGBM', 'autoLoadGBM', 'autoEquipGBM') and values[key + 'Cost'] == 0:
                    battleStatText = battleStatText.replace('{{%s}}' % key, '')
                else:
                    battleStatText = battleStatText.replace('{{%s}}' % key, userMacros[key])

            message = message + "<font color='#929290'>" + battleStatText + "</font>"
            item['message'] = self.formatString(message, stats)
            if self.config.get('overwriteBattleResultBgIcon', False):
                item['message']['bgIcon'] = self.config.get(
                  {-1: 'bgIconDefeat', 0: 'bgIconDraw', 1: 'bgIconWin'}[stats['values']['result']], item['message']['bgIcon']
                )

    def filterNotificationList(self, item):
        message = item['message'].get('message', '')
        msg = unicode(message, 'utf-8') if isinstance(message, str) else (message if isinstance(message, unicode) else None)
        if msg:
            for pattern in self.config.get('hideMessagePatterns', []):
                if re.search(pattern, msg, re.I):
                    return False

        return True

    def getAccountStats(self):
        vehiclesStatistics = []
        for intCD, dossier in g_itemsCache.items.getVehicleDossiersIterator():
            s = VehicleDossier(dossier, intCD).getRandomStats()
            try:
                vt = vehiclesWG.getVehicleType(intCD)
            except KeyError:
                if s.getBattlesCount()>0:
                    LOG_NOTE('No vehicle with intCD=' + str(intCD) + ' (' + str(s.getBattlesCount()) + ')')
            else:
                v = s._stats.expand()._StaticDossierBlockDescr__data.copy()
                v.update(s._stats2.expand()._StaticDossierBlockDescr__data)
                v.update(s._statsMax.expand()._StaticDossierBlockDescr__data)
                v.update({
                  'idNum': intCD,
                  'tier': vt.level,
                  'vehicle-raw': vt.name.replace(':', '-'),
                  'vehicle-short': vt.shortUserString,
                  'vehicle-long': vt.userString,
                })
                vehiclesStatistics.append(v)
        self.account = self.calcWN8(vehiclesStatistics, False)
        self.account['_type'] = 'account'
        self.save()


def handleLobbyViewLoaded(_):
    LOG_NOTE('handleLobbyViewLoaded start')
    stat.load()
    stat.battleResultsAvailable.set()
    LOG_NOTE('handleLobbyViewLoaded end')

g_eventBus.addListener(events.GUICommonEvent.LOBBY_VIEW_LOADED, handleLobbyViewLoaded)

def onAccountBecomeNonPlayer():
    # TODO why it triggers twice???
    #LOG_NOTE('onAccountBecomeNonPlayer start')
    stat.battleResultsAvailable.clear()
    #LOG_NOTE('onAccountBecomeNonPlayer end')

g_playerEvents.onAccountBecomeNonPlayer += onAccountBecomeNonPlayer

old_nlv_getMessagesList = NotificationListView._NotificationListView__getMessagesList

def new_nlv_getMessagesList(self):
    result = old_nlv_getMessagesList(self)
    if stat.config.get('onlineReloadConfig', False):
        stat.readConfig()
        stat.updateMessage()
    if self._NotificationListView__currentGroup in 'info':
        result.append(stat.createMessage())
    return result

from notification.settings import NOTIFICATION_GROUP
old_nlv_setNotificationList = NotificationListView._NotificationListView__setNotificationList

def new_nlv_setNotificationList(self):
    if stat.config.get('onlineReloadConfig', False):
        stat.readConfig()
        stat.updateMessage()
    formedList = self._NotificationListView__getMessagesList()
    if len(stat.config.get('hideMessagePatterns', [])):
        formedList = filter(stat.filterNotificationList, formedList)
    self.as_setMessagesListS({'messages': formedList,
     'emptyListText': self._NotificationListView__getEmptyListMsg(len(formedList) > 0),
     'btnBarSelectedIdx': NOTIFICATION_GROUP.ALL.index(self._NotificationListView__currentGroup)})
    self._model.resetNotifiedMessagesCount(self._NotificationListView__currentGroup)

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
        if stat.useParametersPanel:
            refreshPanelDisplay()
        if stat.useMessenger:
            nlv.as_updateMessageS(stat.createMessage())

def new_onClickPopup(self, typeID, entityID, action):
    if action == URLLINK:
        BigWorld.wg_openWebBrowser(action)
    else:
        old_npuv_onClickPopup(self, typeID, entityID, action)

old_npuv_sendMessageForDisplay = NotificationPopUpViewer._NotificationPopUpViewer__sendMessageForDisplay

def new_npuv_sendMessageForDisplay(self, notification):
    if stat.config.get('showPopUp', True):
        old_npuv_sendMessageForDisplay(self, notification)

vehicleParams = None
expandedStatisticsGroups = {'parameters': False, 'research': True, 'statistics': True, 'vehicles': False}
separator = {'state': 'separator', 'isEnabled': False, 'tooltip': ''}

def refreshPanelDisplay():
    if vehicleParams and vehicleParams._vehParamsDP:
        vehicleParams.update()

from gui.Scaleform.daapi.view.lobby.hangar.VehicleParameters import _VehParamsGenerator, VehicleParameters
#from gui.shared.items_parameters.params_helper import VehParamsBaseGenerator
from account_helpers.AccountSettings import AccountSettings
from gui.shared.items_parameters import RELATIVE_PARAMS
from gui.shared.items_parameters.params_helper import PARAMS_GROUPS

def getFormattedParams(self, comparator, expandedGroups = None, vehIntCD = None):
    result = []
    panelTitles = stat.config.get("panelTitles", {"parameters": "Vehicle Parameters", "statistics": "Statistics", "research": "Research", "vehicles": "Session Statistics by Tank"})
    if expandedStatisticsGroups['parameters']:
        result.extend([{
          'buffIconSrc': '',
          'isOpen': True,
          'isEnabled': True,
          'tooltip': '',
          'state': 'simpleTop',
          'paramID': 'parameters',
          'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['parameters'] + "</font>",
          'valueText': "<font></font>"
        },separator]) #,VehParamsBaseGenerator.getFormattedParams(self, comparator, expandedGroups, vehIntCD)])
        for groupIdx, groupName in enumerate(RELATIVE_PARAMS):
            relativeParam = comparator.getExtendedData(groupName)
            isOpened = expandedGroups is None or expandedGroups.get(groupName, False)
            result.append(self._makeSimpleParamHeaderVO(relativeParam, isOpened, comparator))
            bottomVo = self._makeSimpleParamBottomVO(relativeParam, vehIntCD)
            if bottomVo:
                result.append(bottomVo)
            if isOpened:
                for paramName in PARAMS_GROUPS[groupName]:
                    param = comparator.getExtendedData(paramName)
                    formattedParam = self._makeAdvancedParamVO(param)
                    if formattedParam:
                        result.append(formattedParam)
        result.append(separator)
    else:
        result.extend([{
          'buffIconSrc': '',
          'isOpen': False,
          'isEnabled': True,
          'tooltip': '',
          'state': 'simpleTop',
          'paramID': 'parameters',
          'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['parameters'] + "</font>",
          'valueText': "<font></font>"
        },separator])

    if researchWatchdogMsg != '':
        if expandedStatisticsGroups['research']:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': True,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'research',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['research'] + "</font>",
              'valueText': "<font></font>"
            },separator])
            for line in researchWatchdogMsg.split('\n'):
                if line=='':
                    result.append(separator)
                else:
                    result.append({
                      'titleText': line,
                      'valueText': "<font></font>",
                      'iconSource': '',
                      'isEnabled': False,
                      'tooltip': '',
                      'state': 'advanced',
                      'paramID': 'research'
                    })
            result.append(separator)
        else:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': False,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'research',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['research'] + "</font>",
              'valueText': "<font></font>"
            },separator])

    if stat.messagePanel != '':
        if expandedStatisticsGroups['statistics']:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': True,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'statistics',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['statistics'] + "</font>",
              'valueText': "<font></font>"
            },separator])
            for line in stat.messagePanel.split('\n'):
                if line=='':
                    result.append(separator)
                else:
                    result.append({
                      'titleText': line,
                      'valueText': "<font></font>",
                      'iconSource': '',
                      'isEnabled': False,
                      'tooltip': '',
                      'state': 'advanced',
                      'paramID': 'statistics'
                    })
            result.append(separator)
        else:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': False,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'statistics',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['statistics'] + "</font>",
              'valueText': "<font></font>"
            },separator])

    if stat.panelByTank != '':
        if expandedStatisticsGroups['vehicles']:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': True,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'vehicles',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['vehicles'] + "</font>",
              'valueText': "<font></font>"
            },separator])
            for line in stat.panelByTank.split('\n'):
                if line=='':
                    result.append(separator)
                else:
                    result.append({
                      'titleText': line,
                      'valueText': "<font></font>",
                      'iconSource': '',
                      'isEnabled': False,
                      'tooltip': '',
                      'state': 'advanced',
                      'paramID': 'vehicles'
                    })
            result.append(separator)
        else:
            result.extend([{
              'buffIconSrc': '',
              'isOpen': False,
              'isEnabled': True,
              'tooltip': '',
              'state': 'simpleTop',
              'paramID': 'vehicles',
              'titleText': "<font face='$TitleFont' size='15' color='#E9E2BF'>" + panelTitles['vehicles'] + "</font>",
              'valueText': "<font></font>"
            },separator])
    return result

def VehicleParameters__init__(self):
    global vehicleParams
    vehicleParams = self
    super(VehicleParameters, self).__init__()
    self._vehParamsDP = None
    self._alreadyShowed = False
    self._expandedGroups = {'relativePower': AccountSettings.getSettings('relativePower'),
         'relativeArmor': AccountSettings.getSettings('relativeArmor'),
         'relativeMobility': AccountSettings.getSettings('relativeMobility'),
         'relativeVisibility': AccountSettings.getSettings('relativeVisibility'),
         'relativeCamouflage': AccountSettings.getSettings('relativeCamouflage')}
    return

def VehicleParameters_onParamClick(self, paramID):
    if paramID in expandedStatisticsGroups:
        expandedStatisticsGroups[paramID] = not expandedStatisticsGroups[paramID]
    else:
        isOpened = not self._expandedGroups[paramID]
        AccountSettings.setSettings(paramID, isOpened)
        self._expandedGroups[paramID] = isOpened
    self._setDPUseAnimAndRebuild(False)

old_getFormattedParams = _VehParamsGenerator.getFormattedParams
VehicleParameters.__init__ = VehicleParameters__init__
VehicleParameters.onParamClick = VehicleParameters_onParamClick

def setHandlers(stat):
    if stat.useMessenger:
        NotificationListView._NotificationListView__getMessagesList = new_nlv_getMessagesList
        NotificationListView._NotificationListView__setNotificationList = new_nlv_setNotificationList
        NotificationListView.onClickAction = new_onClickAction
        NotificationPopUpViewer.onClickAction = new_onClickPopup
        NotificationPopUpViewer._NotificationPopUpViewer__sendMessageForDisplay = new_npuv_sendMessageForDisplay
    if stat.useParametersPanel:
        _VehParamsGenerator.getFormattedParams = getFormattedParams
    else:
        _VehParamsGenerator.getFormattedParams = old_getFormattedParams
    refreshPanelDisplay()

from gui.battle_results.service import BattleResultsService

def new_getResultsVO(self, arenaUniqueID):
    vo = old_getResultsVO(self, arenaUniqueID)
    template = stat.config.get('battleResultWindowTitleExtension', None)
    if template:
        stats = stat.battleStats.get(arenaUniqueID, None)
        if stats:
            arenaStr = vo['common']['arenaStr']
            template = template.replace('{{arenaStr}}', arenaStr)
            vo['common']['arenaStr'] = stat.formatString(template, stats)
    return vo

old_getResultsVO = BattleResultsService.getResultsVO
BattleResultsService.getResultsVO = new_getResultsVO

from chat_shared import SYS_MESSAGE_TYPE

mt_battleResults = SYS_MESSAGE_TYPE.battleResults.index()

from messenger.formatters import collections_by_type

# we will format it on our own
from messenger.formatters.service_channel import BattleResultsFormatter

class DummyBattleResultsFormatter(BattleResultsFormatter):
    @async
    def format(self, message, callback):
        callback(('', None))

battleResults_formatter = collections_by_type.SERVER_FORMATTERS[mt_battleResults]
collections_by_type.SERVER_FORMATTERS[mt_battleResults] = DummyBattleResultsFormatter()

def onChatMessageReceived(id, message):
    if message.type==mt_battleResults:
        arenaUniqueID = message.data.get('arenaUniqueID', 0)
        LOG_NOTE('putting new arenaUniqueID onto the queue %s' % str(arenaUniqueID))
        stat.queue.put((arenaUniqueID, lambda: createBattleResultMessage(arenaUniqueID, message)))
        if hasattr(BigWorld.player(), 'arena') and stat.config.get('enableBattleEndedMessage', True):
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

g_messengerEvents.serviceChannel.onChatMessageReceived += onChatMessageReceived

@process
def createBattleResultMessage(arenaUniqueID, message):
    formatted, settings = yield battleResults_formatter.format(message)
    if stat.config.get('showStatForBattle', True):
        stat.replaceBattleResultMessage(formatted, arenaUniqueID)
    # code from ServiceChannelManager.__addServerMessage
    serviceChannelManager = MessengerEntry.g_instance.protos.BW.serviceChannel
    clientID = serviceChannelManager._ServiceChannelManager__idGenerator.next()
    serviceChannelManager._ServiceChannelManager__messages.append((clientID, (True, formatted, settings)))
    serviceChannelManager._ServiceChannelManager__unreadMessagesCount += 1
    serviceChannelEvents = g_messengerEvents.serviceChannel
    serviceChannelEvents.onServerMessageReceived(clientID, formatted, settings)
    customEvent = settings.getCustomEvent()
    if customEvent is not None:
        serviceChannelEvents.onCustomMessageDataReceived(clientID, customEvent)

def showConfirmDialog(message, callback):
    DialogsInterface.showDialog(SimpleDialogMeta(title="Confirm", message=message, buttons=I18nConfirmDialogButtons()), callback)

from gui.battle_control import arena_visitor
from gui.battle_control import avatar_getter

def new__BattleSessionProvider__pe_onBattleResultsReceived(self, isActiveVehicle, _):
    if isActiveVehicle:
        arenaUniqueID = self._BattleSessionProvider__arenaVisitor.getArenaUniqueID()
        LOG_NOTE('Try to exit from arena', arenaUniqueID)
        if arenaUniqueID:
            #self.__ctx.lastArenaUniqueID = arenaUniqueID
            stat.lastArenaUniqueID = arenaUniqueID
        avatar_getter.leaveArena()

BattleSessionProvider._BattleSessionProvider__pe_onBattleResultsReceived = new__BattleSessionProvider__pe_onBattleResultsReceived

stat = SessionStatistic()

# research watchdog

researchWatchdogMsg = ''

if stat.configIsValid and stat.enableResearchWatchdog:
    config = stat.config.get("researchWatchdog", {})
    if config:
        from items import ITEM_TYPE_INDICES, ITEM_TYPE_NAMES
        from skeletons.connection_mgr import IConnectionManager
        from CurrentVehicle import g_currentVehicle
        from gui.Scaleform.daapi.view.lobby.techtree import dumpers
        from gui.Scaleform.daapi.view.lobby.techtree.settings import NODE_STATE
        from gui.Scaleform.genConsts.NODE_STATE_FLAGS import NODE_STATE_FLAGS
        from gui.Scaleform.daapi.view.lobby.techtree.data import ResearchItemsData
        
        _VEHICLE = ITEM_TYPE_INDICES['vehicle']

        last_intCD1 = None
        alerted = {}
        itemTypeNames = []

        def MYLOG(*args):
            LOG_NOTE("%s" % time.strftime('%Y-%m-%d %H:%M:%S'), *args)
            pass

        def onCurrentVehicle(*args):
            global last_intCD1
            MYLOG("onCurrentVehicle%s" % str(args))
            if last_intCD1 is None or last_intCD1 != g_currentVehicle.item.intCD:
                last_intCD1 = g_currentVehicle.item.intCD
                MYLOG("g_currentVehicle.invID .item.intCD", g_currentVehicle.invID, last_intCD1)
                onXpChanged()

        def onXpChanged(*args):
            global researchWatchdogMsg
            MYLOG("onXpChanged")
            if not (g_currentVehicle and g_currentVehicle.item):
                MYLOG("no g_currentVehicle.item")
                BigWorld.callback(1, onXpChanged)
                return
            intCD = g_currentVehicle.item.intCD
            if g_currentVehicle.item.isFullyElite:
                if researchWatchdogMsg != "":
                    researchWatchdogMsg = ""
                    refreshPanelDisplay()
                msg = config.get("warnIfEliteAndNoCrewAcc", "")
                if not g_currentVehicle.item.isXPToTman and msg != "":
                    if not alerted.get(intCD, False):
                        alerted[intCD] = True
                        SystemMessages.pushMessage(msg, SystemMessages.SM_TYPE.Warning, config.get("warnUsingAlertBox", False))
                return
            #startTime = time.time()
            lastResearchWatchdogMsg = researchWatchdogMsg
            rid = ResearchItemsData(dumpers.ResearchItemsObjDumper())
            rid.setRootCD(intCD)
            rid.load()
            msg = ""
            msgpart = config.get("msgItem", "%(item)s")
            altmsg = ""
            altmsgpart = config.get("notifyOfLockedModulesMsgItem", "%(xp)s xp left for %(item)s")
            #MYPPRINT(rid._nodes, "rid._nodes")
            if config.get("useFreeXp", True):
                next2unlock = filter(lambda item: NODE_STATE_FLAGS.ENOUGH_XP & item['state'], rid._nodes)
                if next2unlock:
                    #MYPPRINT(next2unlock, "next2unlock ENOUGH_XP")
                    for item in next2unlock:
                        itemid = int(item['id'])
                        oitem = g_itemsCache.items.getItemByCD(itemid)
                        msg = msg + "\n" + (msgpart % {
                            "item": trunc(itemTypeName(oitem.itemTypeID) + ': ' + oitem.shortUserName)
                        })
                next2unlock = filter(lambda item: NODE_STATE_FLAGS.NEXT_2_UNLOCK & item['state'], rid._nodes)
                if next2unlock:
                    #MYPPRINT(next2unlock, "next2unlock NEXT_2_UNLOCK")
                    xp = g_currentVehicle.item.xp
                    for item in next2unlock:
                        if not xp >= item['unlockProps'].xpCost:
                            itemid = int(item['id'])
                            oitem = g_itemsCache.items.getItemByCD(itemid)
                            #MYPPRINT(oitem)
                            xp_left = "{:,}".format(item['unlockProps'].xpCost - xp).replace(',', ' ')
                            altmsg = altmsg + "\n" + (altmsgpart % {
                                "xp": xp_left,
                                "item": trunc(itemTypeName(oitem.itemTypeID) + ': ' + oitem.shortUserName)
                            })
            else:
                next2unlock = filter(lambda item: NODE_STATE_FLAGS.NEXT_2_UNLOCK & item['state'], rid._nodes)
                if next2unlock:
                    xp = g_currentVehicle.item.xp
                    for item in next2unlock:
                        itemid = int(item['id'])
                        oitem = g_itemsCache.items.getItemByCD(itemid)
                        #MYPPRINT(oitem)
                        if xp >= item['unlockProps'].xpCost:
                            msg = msg + "\n" + (msgpart % {
                                "item": trunc(itemTypeName(oitem.itemTypeID) + ': ' + oitem.shortUserName)
                            })
                        else:
                            xp_left = "{:,}".format(item['unlockProps'].xpCost - xp).replace(',', ' ')
                            altmsg = altmsg + "\n" + (altmsgpart % {
                                "xp": xp_left,
                                "item": trunc(itemTypeName(oitem.itemTypeID) + ': ' + oitem.shortUserName)
                            })
            if altmsg != "" and config.get("notifyOfLockedModules", True):
                altmsg = config.get("notifyOfLockedModulesMsg", "Item(s) yet to be researched:") + altmsg
                if msg != "":
                    msg = msg + "\n\n" + altmsg
                else:
                    researchWatchdogMsg = altmsg
            if msg != "":
                researchWatchdogMsg = config.get("msg", "Item(s) ready to be researched:") + msg
            elif altmsg == "":
                researchWatchdogMsg = ""
            if researchWatchdogMsg != "":
                userMacros = stat.config.get('userMacros', {})
                for key in userMacros.keys():
                    researchWatchdogMsg = researchWatchdogMsg.replace('{{%s}}' % key, userMacros[key])
            if lastResearchWatchdogMsg != researchWatchdogMsg:
                refreshPanelDisplay()
            #_LOG_EXECUTING_TIME(startTime, 'onXpChanged')
            
        def myOnAvatarBecomeNonPlayer(*args):
            g_currentVehicle.onChanged += onCurrentVehicle

        def trunc(data):
            maxlen = config.get("maxCharsPerItem", 50)
            return (data[:maxlen] + config.get("cutOffSymbol", '..')) if len(data) > maxlen else data
            
        def itemTypeName(itemTypeID):
            try:
                return itemTypeNames[itemTypeID]
            except IndexError:
                return "%d?" % itemTypeID

        def connectionManager_onConnected(*args):
            #MYLOG("connectionManager_onConnected%s" % str(args))
            g_currentVehicle.onChanged += onCurrentVehicle
            g_playerEvents.onBattleResultsReceived += onXpChanged
            g_playerEvents.onVehicleBecomeElite += onXpChanged
            g_playerEvents.onAvatarBecomeNonPlayer += myOnAvatarBecomeNonPlayer

        config.update(config.get(getClientLanguage(), config.get("en", {})))
        itemTypeNames = config.get("itemTypeNames", ITEM_TYPE_NAMES)
        connectionManager = dependency.instance(IConnectionManager)
        connectionManager.onConnected += connectionManager_onConnected
