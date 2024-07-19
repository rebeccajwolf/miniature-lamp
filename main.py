import json
import os
import json
import builtins
import platform
import random
import secrets
import subprocess
import sys
import time
import re
import urllib.parse
import contextlib
import dbm.dumb
import shelve
import wget
import zipfile
from argparse import ArgumentParser
import datetime as dt1
from datetime import date, datetime, timedelta
from enum import Enum, auto
from itertools import cycle
from pathlib import Path
from typing import Union, List, Literal, Final, NamedTuple
import copy
from pytz import timezone
import traceback
import ipapi
import requests
import psutil
import pyotp
from requests_oauthlib import OAuth2Session
from functools import wraps
from func_timeout import FunctionTimedOut, func_set_timeout
from notifiers import get_notifier
from random_word import RandomWords
from userAgentGenerator import GenerateUserAgent
from keep_alivev2 import keep_alive
from selenium import webdriver as edgedriver
import undetected_chromedriver as uc
from selenium import webdriver
from selenium.common.exceptions import (ElementNotInteractableException, NoAlertPresentException,
                                        NoSuchElementException, SessionNotCreatedException, TimeoutException,
                                        UnexpectedAlertPresentException, JavascriptException,
                                        ElementNotVisibleException, ElementClickInterceptedException, WebDriverException)
from selenium.webdriver.chrome.webdriver import WebDriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.remote.webelement import WebElement
from selenium.webdriver.support import expected_conditions as ec
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.chrome.service import Service as ChromeService
from selenium.webdriver.edge.service import Service as EdgeService
from pyvirtualdisplay import Display
from webdriver_manager.chrome import ChromeDriverManager
from webdriver_manager.core.os_manager import ChromeType
from webdriver_manager.microsoft import EdgeChromiumDriverManager
import tkinter as tk
from tkinter import messagebox, ttk
from math import ceil
from exceptions import *


# Define user-agents
PC_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Safari/537.36 Edg/110.0.1587.41'
MOBILE_USER_AGENT = 'Mozilla/5.0 (Linux; Android 12; SM-N9750) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.5481.63 Mobile Safari/537.36 EdgA/109.0.1518.70'

POINTS_COUNTER = 0
STARTING_POINTS = 0

# Global variables
# added accounts when finished or those have same date as today date in LOGS at beginning.
FINISHED_ACCOUNTS = []
ERROR = True  # A flag for when error occurred.
# A flag for when the account has mobile bing search, it is useful for accounts level 1 to pass mobile.
MOBILE = True
CURRENT_ACCOUNT = None  # save current account into this variable when farming.
LOGS = {}  # Dictionary of accounts to write in 'logs_accounts.txt'.
FAST = False  # When this variable set True then all possible delays reduced.
SUPER_FAST = False  # fast but super
BASE_URL = "https://rewards.bing.com/"
START_TIME = float(5)
END_TIME = float(13)
LOGIN_URL = os.environ.get("URL", "https://rewards.bing.com/Signin/")
REDEEMABLE = False

# Auto Redeem - Define max amount of auto-redeems per run and counter
MAX_REDEEMS = 1
auto_redeem_counter = 0


def isProxyWorking(proxy: str) -> bool:
    """Check if proxy is working or not"""
    try:
        requests.get("https://www.google.com/",
                     proxies={"https": proxy}, timeout=5)
        return True
    except:
        return False

def downloadWebDriver():
    # get the latest chrome driver version number
    url = 'https://chromedriver.storage.googleapis.com/LATEST_RELEASE'
    response = requests.get(url)
    version_number = response.text

    # build the donwload url
    download_url = "https://chromedriver.storage.googleapis.com/" + version_number +"/chromedriver_linux64.zip"

    # download the zip file using the url built above
    latest_driver_zip = wget.download(download_url,'chromedriver.zip')

    # extract the zip file
    with zipfile.ZipFile(latest_driver_zip, 'r') as zip_ref:
        zip_ref.extractall() # you can specify the destination folder path here
    # delete the zip file downloaded above
    os.remove(latest_driver_zip)

def createDisplay():
    """Create Display"""
    try:
        display = Display(visible=False, size=(1920, 1080))
        display.start()
    except Exception as exc:  # skipcq
        prYellow("Virtual Display Failed!")
        prRed(exc if ERROR else "")

def hide_email(email: str):
    email_parts = email.split('@')
    return f'{email_parts[0][:3]}{"*"*(len(email_parts[0])-3)}{email_parts[0][-3:]}@{email_parts[1]}'

def wait():
    currentHour = dt1.datetime.now(timezone('America/New_York')).hour
    if not (currentHour >= START_TIME and currentHour < END_TIME):
        range = (START_TIME-currentHour) if (currentHour < START_TIME) else ((24 - currentHour) + START_TIME)
        time.sleep((range) * 3600)
    return


def retry_on_500_errors(function):
    @wraps(function)
    def wrapper(*args, **kwargs):
        driver: WebDriver = args[0]
        error_codes = ["HTTP ERROR 500", "HTTP ERROR 502",
                       "HTTP ERROR 503", "HTTP ERROR 504", "HTTP ERROR 505"]
        status_code = "-"
        result = function(*args, **kwargs)
        while True:
            try:
                status_code = driver.execute_script(
                    "return document.readyState;")
                if status_code == "complete" and not any(error_code in driver.page_source for error_code in error_codes):
                    return result
                elif status_code == "loading":
                    return result
                else:
                    raise Exception("Page not loaded")
            except Exception as e:
                # Check if the page contains 500 errors
                if any(error_code in driver.page_source for error_code in error_codes):
                    driver.refresh()  # Recursively refresh
                else:
                    raise Exception(
                        f"another exception occurred during handling 500 errors with status '{status_code}': {e}")
    return wrapper


def browserSetup(isMobile: bool = False, proxy: str = None) -> WebDriver:
    """Create Chrome browser"""
    user_agent = GenerateUserAgent().userAgent(browserConfig={}, mobile=isMobile)[0]
    from selenium.webdriver.edge.options import Options as EdgeOptions
    if ARGS.edge:
        options = EdgeOptions()
    else:
        options = uc.ChromeOptions()
    if not isMobile:
        user_data = f'--user-data-dir={Path(__file__).parent}/Profiles/{CURRENT_ACCOUNT}/PC'
    else:
        user_data = f'--user-data-dir={Path(__file__).parent}/Profiles/{CURRENT_ACCOUNT}/Mobile'
    options.add_argument("--user-agent=" + user_agent)
    options.add_argument('--lang=' + LANG.split("-")[0])
    prefs = {"profile.default_content_setting_values.geolocation" :2,
                    "profile.default_content_setting_values.notifications": 2,
                    "credentials_enable_service": False,
                    "profile.password_manager_enabled": False}
    if ARGS.no_images:
        prefs["profile.managed_default_content_settings.images"] = 2
    if ARGS.account_browser:
        prefs["detach"] = True
    if proxy is not None:
        if isProxyWorking(proxy):
            options.add_argument(f'--proxy-server={proxy}')
            prBlue(f"Using proxy: {proxy}")
        else:
            if ARGS.recheck_proxy:
                prYellow(
                    "[PROXY] Your entered proxy is not working, rechecking the provided proxy.")
                time.sleep(5)
                if isProxyWorking(proxy):
                    options.add_argument(f'--proxy-server={proxy}')
                    prBlue(f"Using proxy: {proxy}")
                elif ARGS.skip_if_proxy_dead:
                    raise ProxyIsDeadException
                else:
                    prYellow(
                        "[PROXY] Your entered proxy is not working, continuing without proxy.")
            elif ARGS.skip_if_proxy_dead:
                raise ProxyIsDeadException
            else:
                prYellow(
                    "[PROXY] Your entered proxy is not working, continuing without proxy.")
    options.add_experimental_option("prefs", prefs)

    options.headless = True if ARGS.headless and ARGS.account_browser is None else False
    options.add_argument("--log-level=3")
    options.add_argument("--blink-settings=imagesEnabled=false")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--ignore-certificate-errors-spki-list")
    options.add_argument("--ignore-ssl-errors")
    options.add_argument("--disable-extensions")
    options.add_argument("--dns-prefetch-disable")
    options.add_argument("--disable-gpu")
    options.add_argument("--disable-default-apps")
    options.add_argument("--disable-features=Translate")
    options.add_argument('--disable-features=PrivacySandboxSettings4')
    if platform.system() == 'Linux':
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
    if ARGS.edge:
        browser = edgedriver.Edge(service=EdgeService(EdgeChromiumDriverManager().install()), options=options)
    else:
        # browser = uc.Chrome(driver_executable_path="chromedriver", options=options, use_subprocess=False, user_data_dir= user_data if ARGS.session or ARGS.account_browser else None, no_sandbox=False)
        browser = uc.Chrome(driver_executable_path="chromedriver.exe", options=options, use_subprocess=False, user_data_dir= user_data if ARGS.session or ARGS.account_browser else None, no_sandbox=False)
    return browser


def browserSetupv2(isMobile: bool = False, proxy: str = None) -> WebDriver:
    """Create Chrome browser"""
    user_agent = GenerateUserAgent().userAgent(browserConfig={}, mobile=isMobile)[0]
    from selenium.webdriver.chrome.options import Options as ChromeOptions
    from selenium.webdriver.edge.options import Options as EdgeOptions
    if ARGS.edge:
        options = EdgeOptions()
    else:
        options = ChromeOptions()
    if ARGS.session or ARGS.account_browser:
        if not isMobile:
            options.add_argument(
                f'--user-data-dir={Path(__file__).parent}/Profiles/{CURRENT_ACCOUNT}/PC')
        else:
            options.add_argument(
                f'--user-data-dir={Path(__file__).parent}/Profiles/{CURRENT_ACCOUNT}/Mobile')
    options.add_argument("--user-agent=" + user_agent)
    options.add_argument('--lang=' + LANG.split("-")[0])
    options.add_argument('--disable-blink-features=AutomationControlled')
    prefs = {"profile.default_content_setting_values.geolocation" :2,
            "profile.default_content_setting_values.notifications": 2,
            "credentials_enable_service": False,
            "profile.password_manager_enabled": False,
            "webrtc.ip_handling_policy": "disable_non_proxied_udp",
             "webrtc.multiple_routes_enabled": False,
             "webrtc.nonproxied_udp_enabled": False}
    if ARGS.no_images:
        prefs["profile.managed_default_content_settings.images"] = 2
    if ARGS.account_browser:
        prefs["detach"] = True
    if proxy is not None:
        if isProxyWorking(proxy):
            options.add_argument(f'--proxy-server={proxy}')
            prBlue(f"Using proxy: {proxy}")
        else:
            if ARGS.recheck_proxy:
                prYellow(
                    "[PROXY] Your entered proxy is not working, rechecking the provided proxy.")
                time.sleep(5)
                if isProxyWorking(proxy):
                    options.add_argument(f'--proxy-server={proxy}')
                    prBlue(f"Using proxy: {proxy}")
                elif ARGS.skip_if_proxy_dead:
                    raise ProxyIsDeadException
                else:
                    prYellow(
                        "[PROXY] Your entered proxy is not working, continuing without proxy.")
            elif ARGS.skip_if_proxy_dead:
                raise ProxyIsDeadException
            else:
                prYellow(
                    "[PROXY] Your entered proxy is not working, continuing without proxy.")
    options.add_experimental_option("prefs", prefs)
    options.add_experimental_option("useAutomationExtension", False)
    options.add_experimental_option("excludeSwitches", ["enable-automation"])
    if ARGS.headless and ARGS.account_browser is None:
        options.add_argument("--headless=new")
    options.add_argument("--log-level=3")
    options.add_argument("--blink-settings=imagesEnabled=false")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--ignore-certificate-errors-spki-list")
    options.add_argument("--ignore-ssl-errors")
    options.add_argument("--disable-extensions")
    options.add_argument("--dns-prefetch-disable")
    options.add_argument("--disable-gpu")
    options.add_argument("--disable-default-apps")
    options.add_argument("--disable-features=Translate")
    options.add_argument('--disable-features=PrivacySandboxSettings4')
    if platform.system() == 'Linux':
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
    if ARGS.edge:
        browser = edgedriver.Edge(service=EdgeService(EdgeChromiumDriverManager().install()), options=options)
    else:
        browser = webdriver.Chrome(options=options)
    return browser


def browserSetupv3(isMobile: bool = False, proxy: str = None) -> WebDriver:
    """Create Chrome browser"""
    def setupProfiles() -> Path:
        """
        Sets up the sessions profile for the chrome browser.
        Uses the username to create a unique profile for the session.

        Returns:
            Path
        """
        sessionsDir = Path(__file__).parent / "sessions"

        # Concatenate username and browser type for a plain text session ID
        sessionid = f"{CURRENT_ACCOUNT}"

        sessionsDir = sessionsDir / sessionid
        sessionsDir.mkdir(parents=True, exist_ok=True)
        return sessionsDir
    user_agent = GenerateUserAgent().userAgent(browserConfig={}, mobile=isMobile)[0]
    from selenium.webdriver.edge.options import Options as EdgeOptions
    if ARGS.edge:
        options = EdgeOptions()
    else:
        options = uc.ChromeOptions()
    user_data = setupProfiles()
    options.add_argument("--user-agent=" + user_agent)
    options.add_argument('--lang=' + LANG.split("-")[0])
    prefs = {"profile.default_content_setting_values.geolocation" :2,
                    "profile.default_content_setting_values.notifications": 2,
                    "credentials_enable_service": False,
                    "profile.password_manager_enabled": False}
    if ARGS.no_images:
        prefs["profile.managed_default_content_settings.images"] = 2
    if ARGS.account_browser:
        prefs["detach"] = True
    if proxy is not None:
        if isProxyWorking(proxy):
            options.add_argument(f'--proxy-server={proxy}')
            prBlue(f"Using proxy: {proxy}")
        else:
            if ARGS.recheck_proxy:
                prYellow(
                    "[PROXY] Your entered proxy is not working, rechecking the provided proxy.")
                time.sleep(5)
                if isProxyWorking(proxy):
                    options.add_argument(f'--proxy-server={proxy}')
                    prBlue(f"Using proxy: {proxy}")
                elif ARGS.skip_if_proxy_dead:
                    raise ProxyIsDeadException
                else:
                    prYellow(
                        "[PROXY] Your entered proxy is not working, continuing without proxy.")
            elif ARGS.skip_if_proxy_dead:
                raise ProxyIsDeadException
            else:
                prYellow(
                    "[PROXY] Your entered proxy is not working, continuing without proxy.")
    options.add_experimental_option("prefs", prefs)

    options.headless = True if ARGS.headless and ARGS.account_browser is None else False
    options.add_argument("--log-level=3")
    # options.add_argument("--incognito")
    options.add_argument("--blink-settings=imagesEnabled=false")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--ignore-certificate-errors-spki-list")
    options.add_argument("--ignore-ssl-errors")
    options.add_argument("--disable-extensions")
    options.add_argument("--dns-prefetch-disable")
    options.add_argument("--disable-gpu")
    options.add_argument("--disable-default-apps")
    options.add_argument("--disable-features=Translate")
    options.add_argument('--disable-features=PrivacySandboxSettings4')
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    # if platform.system() == 'Linux':
    #     options.add_argument("--no-sandbox")
    #     options.add_argument("--disable-dev-shm-usage")
    if ARGS.edge:
        browser = edgedriver.Edge(service=EdgeService(EdgeChromiumDriverManager().install()), options=options)
    else:
        # browser = uc.Chrome(driver_executable_path="chromedriver", options=options, use_subprocess=False, user_data_dir= user_data if ARGS.session or ARGS.account_browser else None, no_sandbox=False)
        browser = uc.Chrome(driver_executable_path="chromedriver", options=options, use_subprocess=False, user_data_dir= user_data.as_posix() if ARGS.session or ARGS.account_browser else None, no_sandbox=False)
    return browser

@retry_on_500_errors
def goToURL(browser: WebDriver, url: str):
    browser.get(url)
    browser.set_page_load_timeout(60)


def displayError(exc: Exception):
    """Display error message with traceback"""
    if ERROR:
        tb = exc.__traceback__
        tb_str = traceback.format_tb(tb)
        error = "\n".join(tb_str).strip() + f"\n{exc}"
        prRed(error)


# Define login function
def login(browser: WebDriver, email: str, pwd: str, totpSecret: str, isMobile: bool = False):

    def answerToBreakFreeFromPassword():
        # Click No thanks on break free from password question
        time.sleep(2)
        browser.find_element(By.ID, "iCancel").click()
        time.sleep(5)

    def answerToSecurityQuestion():
        # Click Looks good on security question
        time.sleep(2)
        browser.find_element(By.ID, 'iLooksGood').click()
        time.sleep(5)

    def answerUpdatingTerms():
        # Accept updated terms
        time.sleep(2)
        browser.find_element(By.ID, 'iNext').click()
        time.sleep(5)

    def waitToLoadBlankPage():
        time.sleep(calculateSleep(10))
        wait = WebDriverWait(browser, 10)
        wait.until(ec.presence_of_element_located((By.TAG_NAME, "body")))
        wait.until(ec.presence_of_all_elements_located)
        wait.until(ec.title_contains(""))
        wait.until(ec.presence_of_element_located(
            (By.CSS_SELECTOR, "html[lang]")))
        wait.until(lambda driver: driver.execute_script(
            "return document.readyState") == "complete")

    def acceptNewPrivacy():
        time.sleep(3)
        waitUntilVisible(browser, By.ID, "id__0", 15)
        browser.execute_script(
            "window.scrollTo(0, document.body.scrollHeight);")
        waitUntilClickable(browser, By.ID, "id__0", 15)
        browser.find_element(By.ID, "id__0").click()
        WebDriverWait(browser, 25).until_not(
            ec.visibility_of_element_located((By.ID, "id__0")))
        time.sleep(5)

    def answerTOTP(totpSecret):
        """Enter TOTP code and submit"""
        if isElementExists(browser, By.ID, 'idTxtBx_SAOTCC_OTC'):
            if totpSecret is not None:
                # Enter TOTP code
                totpCode = pyotp.TOTP(totpSecret).now()
                browser.find_element(
                    By.ID, "idTxtBx_SAOTCC_OTC").send_keys(totpCode)
                print('[LOGIN]', 'Writing TOTP code...')
                # Click submit
                browser.find_element(By.ID, 'idSubmit_SAOTCC_Continue').click()
            else:
                print('[LOGIN]', 'TOTP code required but no secret was provided.')
            # Wait 5 seconds
            time.sleep(5)
            if isElementExists(browser, By.ID, 'idTxtBx_SAOTCC_OTC'):
                raise TOTPInvalidException

    # Close welcome tab for new sessions
    if ARGS.session:
        time.sleep(2)
        if len(browser.window_handles) > 1:
            current_window = browser.current_window_handle
            for handler in browser.window_handles:
                if handler != current_window:
                    browser.switch_to.window(handler)
                    time.sleep(0.5)
                    browser.close()
            browser.switch_to.window(current_window)
    time.sleep(1)
    while True:
        # Access to bing.com
        goToURL(browser, LOGIN_URL)
        time.sleep(calculateSleep(15))
        # Check if account is already logged in
        if ARGS.session:
            if browser.title == "":
                waitToLoadBlankPage()
            if browser.title == "Microsoft account privacy notice" or isElementExists(browser, By.XPATH, '//*[@id="interruptContainer"]/div[3]/div[3]/img'):
                acceptNewPrivacy()
            if browser.title == "We're updating our terms" or isElementExists(browser, By.ID, 'iAccrualForm'):
                answerUpdatingTerms()
            if browser.title == 'Is your security info still accurate?' or isElementExists(browser, By.ID, 'iLooksGood'):
                answerToSecurityQuestion()
            # Click No thanks on break free from password question
            if isElementExists(browser, By.ID, "setupAppDesc") or browser.title == "Break free from your passwords":
                answerToBreakFreeFromPassword()
            if browser.title == 'Microsoft account | Home' or isElementExists(browser, By.CSS_SELECTOR, 'html[data-role-name="RewardsPortal"]'):
                prGreen('[LOGIN] Account already logged in !')
                checkRewardsLogin(browser)
                print('[LOGIN]', 'Ensuring login on Bing...')
                checkBingLogin(browser)
                return
            elif browser.title == 'Your account has been temporarily suspended' or browser.current_url.startswith("https://account.live.com/Abuse"):
                raise AccountLockedException
            elif browser.title == "Help us protect your account" or browser.current_url.startswith(
                    "https://account.live.com/proofs/Add"):
                handleUnusualActivity(browser, isMobile)
                return
            elif browser.title == "Help us secure your account" or browser.current_url.startswith("https://account.live.com/recover"):
                raise UnusualActivityException
            elif isElementExists(browser, By.ID, 'mectrl_headerPicture') or 'Sign In or Create' in browser.title:
                browser.find_element(By.ID, 'mectrl_headerPicture').click()
                waitUntilVisible(browser, By.ID, 'i0118', 15)
                if isElementExists(browser, By.ID, 'i0118'):
                    browser.find_element(By.ID, "i0118").send_keys(pwd)
                    time.sleep(2)
                    browser.find_element(By.ID, 'idSIButton9').click()
                    time.sleep(5)
                    answerTOTP(totpSecret)
                    prGreen('[LOGIN] Account logged in again !')
                    print('[LOGIN]', 'Ensuring login on Bing...')
                    checkBingLogin(browser)
                    return
        # Wait complete loading
        waitUntilVisible(browser, By.ID, 'i0116', 10)
        # Enter email
        print('[LOGIN]', 'Writing email...')
        browser.find_element(By.NAME, "loginfmt").send_keys(email)
        # Click next
        browser.find_element(By.ID, 'idSIButton9').click()
        # Wait 2 seconds
        time.sleep(calculateSleep(5))
        if isElementExists(browser, By.ID, "usernameError"):
            raise InvalidCredentialsException
        # Wait complete loading
        waitUntilVisible(browser, By.ID, 'i0118', 10)
        # Enter password
        time.sleep(3)
        browser.find_element(By.ID, "i0118").send_keys(pwd)
        # browser.execute_script("document.getElementById('i0118').value = '" + pwd + "';")
        print('[LOGIN]', 'Writing password...')
        # Click next
        browser.find_element(By.ID, 'idSIButton9').click()
        # Wait 5 seconds
        time.sleep(7)
        if isElementExists(browser, By.ID, "i0118Error"):
            raise InvalidCredentialsException
        answerTOTP(totpSecret)
        tooManyRequests = browser.find_element(By.TAG_NAME, "body").text
        # print(f'Too Many Requests INFO = {tooManyRequests}')
        if not "Too Many Requests" in tooManyRequests:
            break
    try:
        if ARGS.session:
            # Click Yes to stay signed in.
            browser.find_element(By.ID, 'acceptButton').click()
        else:
            # Click No.
            browser.find_element(By.ID, 'declineButton').click()
    except NoSuchElementException:
        # Check for if account has been locked.
        if (
            browser.title == "Your account has been temporarily suspended" or
            isElementExists(browser, By.CLASS_NAME, "serviceAbusePageContainer  PageContainer") or
            browser.current_url.startswith("https://account.live.com/Abuse")
        ):
            raise AccountLockedException
        elif browser.title == "Help us protect your account" or \
                browser.current_url.startswith("https://account.live.com/proofs/Add"):
            handleUnusualActivity(browser, isMobile)
            return
        elif browser.title == "Help us secure your account" or browser.current_url.startswith("https://account.live.com/recover"):
            raise UnusualActivityException
    else:
        if browser.title == "Microsoft account privacy notice" or isElementExists(browser, By.XPATH, '//*[@id="interruptContainer"]/div[3]/div[3]/img'):
            acceptNewPrivacy()
        if browser.title == "":
            waitToLoadBlankPage()
        if browser.title == "We're updating our terms" or isElementExists(browser, By.ID, 'iAccrualForm'):
            answerUpdatingTerms()
        if browser.title == 'Is your security info still accurate?' or isElementExists(browser, By.ID, 'iLooksGood'):
            answerToSecurityQuestion()
        # Click No thanks on break free from password question
        if isElementExists(browser, By.ID, "setupAppDesc") or browser.title == "Break free from your passwords":
            answerToBreakFreeFromPassword()
    # Wait 5 seconds
    time.sleep(5)
    # Click Security Check
    print('[LOGIN]', 'Passing security checks...')
    try:
        browser.find_element(By.ID, 'iLandingViewAction').click()
    except (NoSuchElementException, ElementNotInteractableException) as e:
        pass
    # Wait complete loading
    try:
        waitUntilVisible(browser, By.ID, 'KmsiCheckboxField', 10)
    except TimeoutException as e:
        pass
    # Click next
    try:
        browser.find_element(By.ID, 'idSIButton9').click()
        # Wait 5 seconds
        time.sleep(5)
    except (NoSuchElementException, ElementNotInteractableException) as e:
        pass
    print('[LOGIN]', 'Logged-in !')
    checkRewardsLogin(browser)
    # Check Login
    print('[LOGIN]', 'Ensuring login on Bing...')
    checkBingLogin(browser)


def checkRewardsLogin(browser: WebDriver):
    """Login into Rewards"""
    global POINTS_COUNTER  # pylint: disable=global-statement
    try:
        time.sleep(calculateSleep(10))
        # click on sign up button if needed
        if isElementExists(browser, By.ID, "start-earning-rewards-link"):
            browser.find_element(By.ID, "start-earning-rewards-link").click()
            time.sleep(5)
            browser.refresh()
            time.sleep(5)
    except:
        pass
    # Check for ErrorMessage
    try:
        browser.find_element(By.ID, 'error').is_displayed()
        # Check wheter account suspended or not
        if 'Your Microsoft Rewards account has been suspended.' in browser.find_element(By.XPATH, '//*[@id="suspendedAccountHeader"]').get_attribute(
                'innerHTML'):
            raise AccountSuspendedException
        # Check whether Rewards is available in your region or not
        elif browser.find_element(By.XPATH, '//*[@id="error"]/h1').get_attribute(
                'innerHTML') == 'Microsoft Rewards is not available in this country or region.':
            raise RegionException
        else:
            error_text = browser.find_element(By.XPATH, '//*[@id="error"]/h1').get_attribute("innerHTML")
            prRed(f"[ERROR] {error_text}")
            raise DashboardException
    except NoSuchElementException:
        pass
    POINTS_COUNTER = getBingAccountPoints(browser)
    handleFirstVisit(browser)


# @func_set_timeout(300)
def checkBingLoginv1(browser: WebDriver):
    """Check if logged in to Bing"""
    goToURL(browser, 'https://www.bing.com/fd/auth/signin?action=interactive&provider=windows_live_id&return_url=https%3A%2F%2Fwww.bing.com%2F')
    time.sleep(calculateSleep(15))
    if not isElementExists(browser, By.XPATH, '//*[@id="id_s" and @aria-hidden="true"]'):
        while True:
            print("Bing Refreshing....")
            goToURL(browser, 'https://www.bing.com/fd/auth/signin?action=interactive&provider=windows_live_id&return_url=https%3A%2F%2Fwww.bing.com%2F')
            time.sleep(calculateSleep(7))
            tryDismissBingCookieBanner(browser)
            try:
                if isElementExists(browser, By.XPATH, '//*[@id="id_s" and @aria-hidden="true"]'):
                    return
            except Exception as exc:
                displayError(exc)
    time.sleep(1)

def checkBingLogin(browser: WebDriver):
        goToURL(browser,
            "https://www.bing.com/fd/auth/signin?action=interactive&provider=windows_live_id&return_url=https%3A%2F%2Fwww.bing.com%2F"
        )
        while True:
            currentUrl = urllib.parse.urlparse(browser.current_url)
            # prBlue(f'Current Bing URL == {currentUrl}')
            if currentUrl.hostname == "www.bing.com" and currentUrl.path == "/":
                # prBlue("in Current URL")
                time.sleep(3)
                tryDismissBingCookieBanner(browser)
                with contextlib.suppress(Exception):
                    if checkIfBingLogin(browser):
                        # prBlue("Checking if Bing Login")
                        return
            time.sleep(1)
            # print("Bing Refreshing....")


def handleUnusualActivity(browser: WebDriver, isMobile: bool = False):
    prYellow('[ERROR] Unusual activity detected !')
    if isElementExists(browser, By.ID, "iShowSkip") and ARGS.skip_unusual:
        try:
            waitUntilClickable(browser, By.ID, "iShowSkip")
            browser.find_element(By.ID, "iShowSkip").click()
        except:
            raise UnusualActivityException
        else:
            prGreen('[LOGIN] Account already logged in !')
            checkRewardsLogin(browser)
            print('[LOGIN]', 'Ensuring login on Bing...')
            checkBingLogin(browser)
            return
    elif isElementExists(browser, By.ID, "iSelectProofAlternate"):
        raise UnusualActivityException
    else:
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Unusual activity detected !'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        if ARGS.telegram or ARGS.discord:
            message = createMessage()
            sendReportToMessenger(message)
        # input('Press any key to close...')
        os._exit(0)


def handleFirstVisit(browser: WebDriver):
    # Pass The Welcome Page.
    try:
        if isElementExists(browser, By.CLASS_NAME, "rewards-slide"):
            try:
                browser.find_element(
                    By.XPATH, "//div[@class='rewards-slide']//a").click()
                time.sleep(calculateSleep(5))
                progress, total = browser.find_element(
                    By.XPATH, "//div[@class='rewards-slide']//mee-rewards-counter-animation/span").get_attribute("innerHTML").split("/")
                progress = int(progress)
                total = int(total)
                if (progress < total):
                    browser.find_element(
                        By.XPATH, "//mee-rewards-welcome-tour//mee-rewards-slide[contains(@class, 'ng-scope') and not(contains(@class,'ng-hide'))]//mee-rewards-check-mark/../a").click()
                    time.sleep(calculateSleep(5))
            except:
                pass

            browser.find_element(
                By.XPATH, "//button[@data-modal-close-button]").click()
            time.sleep(calculateSleep(5))
    except:
        print('[LOGIN]', "Can't pass the first time quiz.")


def tryDismissCookieBanner(browser: WebDriver):
    # Try to dismiss the cookie banner
    with contextlib.suppress(Exception):
        browser.find_element(By.ID, "cookie-banner").find_element(
            By.TAG_NAME, "button"
        ).click()
        time.sleep(2)

def getBingInfo(browser: WebDriver):
    # Get Bing information using cookies
    cookieJar = browser.get_cookies()
    cookies = {cookie["name"]: cookie["value"] for cookie in cookieJar}
    maxTries = 5
    for _ in range(maxTries):
        try:
            response = requests.get(
                "https://www.bing.com/rewards/panelflyout/getuserinfo",
                cookies=cookies,
            )
            if response.status_code == requests.codes.ok:
                return response.json()
        except Exception as exc:
            displayError(exc)
        time.sleep(1)
    return None

def checkIfBingLogin(browser: WebDriver):
    # Check if the user is logged in to Bing
    try:
        if data := getBingInfo(browser):
            # prBlue(f'Bing Login Info = {data["userInfo"]["isRewardsUser"]}')
            return data["userInfo"]["isRewardsUser"]
        else:
            return False
    except Exception as exc:
        displayError(exc)

def tryDismissBingCookieBanner(browser: WebDriver):
    # Try to dismiss the Bing cookie banner
    with contextlib.suppress(Exception):
        browser.find_element(By.ID, "bnp_btn_accept").click()
        time.sleep(2)

def waitUntilVisible(browser: WebDriver, by_: By, selector: str, time_to_wait: int = 10):
    """Wait until visible"""
    WebDriverWait(browser, time_to_wait).until(
        ec.visibility_of_element_located((by_, selector)))

def close_all_but_main(browser: WebDriver):
    """
    Closes all other windows and switches focus back to main window
    :return: None
    """
    try:
        if len(browser.window_handles) == 1:
            return
        for _ in range(len(browser.window_handles)-1):
            browser.switch_to.window(browser.window_handles[-1])
            browser.close()
    except WebDriverException:
        print('Error when switching to main_window')
    finally:
        browser.switch_to.window(browser.window_handles[0])

def goto_latest_window(browser: WebDriver, time_to_wait: int = 0):
    """
    Switches to newest open window
    :return:
    """
    browser.switch_to.window(browser.window_handles[-1])
    if time_to_wait > 0:
        time.sleep(time_to_wait)


def waitUntilClickable(browser: WebDriver, by_: By, selector: str, time_to_wait: int = 10):
    """Wait until clickable"""
    WebDriverWait(browser, time_to_wait).until(
        ec.element_to_be_clickable((by_, selector)))


def waitUntilQuestionRefresh(browser: WebDriver):
    """Wait until question refresh"""
    tries = 0
    refreshCount = 0
    while True:
        try:
            browser.find_elements(By.CLASS_NAME, 'rqECredits')[0]
            return True
        except:
            if tries < 10:
                tries += 1
                time.sleep(0.5)
            else:
                if refreshCount < 5:
                    browser.refresh()
                    refreshCount += 1
                    tries = 0
                    time.sleep(5)
                else:
                    return False


def waitUntilQuizLoads(browser: WebDriver):
    """Wait until quiz loads"""
    tries = 0
    refreshCount = 0
    while True:
        try:
            browser.find_element(
                By.XPATH, '//*[@id="currentQuestionContainer"]')
            return True
        except:
            if tries < 10:
                tries += 1
                time.sleep(0.5)
            else:
                if refreshCount < 5:
                    browser.refresh()
                    refreshCount += 1
                    tries = 0
                    time.sleep(5)
                else:
                    return False


def findBetween(s: str, first: str, last: str) -> str:
    """Find between"""
    try:
        start = s.index(first) + len(first)
        end = s.index(last, start)
        return s[start:end]
    except ValueError:
        return ""


def getCCodeLangAndOffset() -> tuple:
    """Get lang, geo, time zone"""
    try:
        nfo = ipapi.location()
        lang = nfo['languages'].split(',')[0]
        geo = nfo['country']
        tz = str(round(int(nfo['utc_offset']) / 100 * 60))
        return lang, geo, tz
    # Due to ipapi limitations it will default to US
    except:
        return 'en-US', 'US', '-480'


def resetTabs(browser: WebDriver):
    """Reset tabs"""
    try:
        curr = browser.current_window_handle

        for handle in browser.window_handles:
            if handle != curr:
                browser.switch_to.window(handle)
                time.sleep(0.5)
                browser.close()
                time.sleep(0.5)

        browser.switch_to.window(curr)
        time.sleep(0.5)
        goToURL(browser, BASE_URL)
        waitUntilVisible(browser, By.ID, 'app-host', 30)
    except:
        goToURL(browser, BASE_URL)
        waitUntilVisible(browser, By.ID, 'app-host', 30)


def getAnswerCode(key: str, string: str) -> str:
    """Get answer code"""
    t = 0
    for i, _ in enumerate(string):
        t += ord(string[i])
    t += int(key[-2:], 16)
    return str(t)


def getDashboardData(browser: WebDriver) -> dict:
    """Get dashboard data"""
    urlBefore = browser.current_url
    tries = 0
    dashboard = None
    while not dashboard and tries <= 5:
        try:
            goToURL(browser, BASE_URL)
            dashboard = browser.execute_script("return dashboard")
        except:
            tries += 1
            if tries == 6:
                raise Exception("[ERROR] Could not get dashboard")
            browser.refresh()
            waitUntilVisible(browser, By.ID, 'app-host', 30)
        finally:
            goToURL(browser, urlBefore)
    return dashboard


def getBingAccountPoints(browser: WebDriver) -> int:
    # Get the Bing account points from the Bing info
    return data["userInfo"]["balance"] if (data := getBingInfo(browser)) else 0

LOAD_DATE_KEY = "loadDate"


class AttemptsStrategy(Enum):
    exponential = auto()
    constant = auto()


class Searches:
    maxAttempts: Final[int] = 8
    baseDelay: Final[float] = 14.0625
    # attemptsStrategy = Final[  # todo Figure why doesn't work with equality below
    attemptsStrategy = AttemptsStrategy.exponential

    def __init__(self, browser: WebDriver, isMobile: bool = False):
        self.browser = browser
        self.isMobile = isMobile

        # dumbDbm = dbm.dumb.open((Path(__file__).parent / "google_trends").__str__(), 'n')
        dumbDbm = dbm.dumb.open((Path(__file__).parent / "google_trends").__str__())
        self.googleTrendsShelf: shelve.Shelf = shelve.Shelf(dumbDbm)
        # print(f"googleTrendsShelf.__dict__ = {self.googleTrendsShelf.__dict__}")
        # print(f"google_trends = {list(self.googleTrendsShelf.items())}")
        loadDate: date | None = None
        if LOAD_DATE_KEY in self.googleTrendsShelf:
            loadDate = self.googleTrendsShelf[LOAD_DATE_KEY]
            # print(
            #     f" after load = {list(self.googleTrendsShelf.items())}"
            # )

        if loadDate is None or loadDate < date.today():
            self.googleTrendsShelf.clear()
            self.googleTrendsShelf[LOAD_DATE_KEY] = date.today()
            trends = self.getGoogleTrends(
                wordsCount=getRemainingSearches(browser=self.browser, desktopAndMobile=True) * random.randint(2,4)
            )
            random.shuffle(trends)
            for trend in trends:
                self.googleTrendsShelf[trend] = None
            # print(
            #     f"google_trends after load = {list(self.googleTrendsShelf.items())}"
            # )

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.googleTrendsShelf.__exit__(None, None, None)

    def getGoogleTrends(self, wordsCount: int) -> list[str]:
        # Function to retrieve Google Trends search terms
        searchTerms: list[str] = []
        i = 0
        while len(searchTerms) < wordsCount:
            i += 1
            # Fetching daily trends from Google Trends API
            r = requests.get(
                f"https://trends.google.com/trends/api/dailytrends?hl={LANG}"
                f'&ed={(date.today() - timedelta(days=i)).strftime("%Y%m%d")}&geo={GEO}&ns=15'
            )
            assert r.status_code == requests.codes.ok
            trends = json.loads(r.text[6:])
            for topic in trends["default"]["trendingSearchesDays"][0][
                "trendingSearches"
            ]:
                searchTerms.append(topic["title"]["query"].lower())
                searchTerms.extend(
                    relatedTopic["query"].lower()
                    for relatedTopic in topic["relatedQueries"]
                )
            searchTerms = list(set(searchTerms))
        del searchTerms[wordsCount : (len(searchTerms) + 1)]
        return searchTerms

    def getRelatedTerms(self, term: str) -> list[str]:
        # Function to retrieve related terms from Bing API
        relatedTerms: list[str] = requests.get(
            f"https://api.bing.com/osjson.aspx?query={term}",
            headers={"User-agent": GenerateUserAgent().userAgent(browserConfig={}, mobile=self.isMobile)[0]},
        ).json()[1]
        if not relatedTerms:
            return [term]
        return relatedTerms

    def bingSearches(self) -> None:
        # Function to perform Bing searches
        print(
            f"[BING] Starting {'Mobile' if self.isMobile else 'Desktop'} Edge Bing searches..."
        )

        goToURL(self.browser, "https://bing.com")
        remainingSearches = getRemainingSearches(self.browser, isMobile=self.isMobile)
        maxSearches = remainingSearches * 2
        searchCount = 0
        while searchCount < remainingSearches and searchCount < maxSearches :
            searchCount = searchCount + 1
            # todo Disable cooldown for first 3 searches (Earning starts with your third search)
            print(f"[BING] {searchCount}/{remainingSearches}")
            
            self.bingSearch()
            time.sleep(random.randint(10, 15))
            if searchCount == remainingSearches:
                print("Checking if Searches Are Really Complete")        
                remainingSearches = getRemainingSearches(self.browser, isMobile=self.isMobile)
                if remainingSearches > 0:
                    print("Adding " + str(remainingSearches) + " Extra Searches")

        print(
            f"[BING] Finished {'Mobile' if self.isMobile else 'Desktop'} Edge Bing searches !"
        )

    def bingSearch(self) -> int:
        # Function to perform a single Bing search
        pointsBefore = getBingAccountPoints(self.browser)

        rootTerm = list(self.googleTrendsShelf.keys())[1]
        terms = self.getRelatedTerms(rootTerm)
        # print(f"terms={terms}")
        termsCycle: cycle[str] = cycle(terms)
        baseDelay = Searches.baseDelay
        # print(f"rootTerm={rootTerm}")

        for i in range(self.maxAttempts + 1):
            if i != 0:
                sleepTime: float
                if Searches.attemptsStrategy == Searches.attemptsStrategy.exponential:
                    sleepTime = baseDelay * 2 ** (i - 1)
                elif Searches.attemptsStrategy == Searches.attemptsStrategy.constant:
                    sleepTime = baseDelay
                else:
                    raise AssertionError
                # print(
                #     f"[BING] Search attempt failed {i}/{Searches.maxRetries}, sleeping {sleepTime}"
                #     f" seconds..."
                # )
                time.sleep(sleepTime)

            waitUntilClickable(
                self.browser, By.ID, "sb_form_q", time_to_wait=20
            )
            searchbar = self.browser.find_element(By.ID, "sb_form_q")
            for _ in range(1000):
                searchbar.click()
                searchbar.clear()
                term = next(termsCycle)
                # print(f"term={term}")
                searchbar.send_keys(term)
                with contextlib.suppress(TimeoutException):
                    WebDriverWait(self.browser, 10).until(
                        ec.text_to_be_present_in_element_value(
                            (By.ID, "sb_form_q"), term
                        )
                    )
                    break
                print("error send_keys")
            else:
                # todo Still happens occasionally, gotta be a fix
                raise TimeoutException
            searchbar.submit()

            pointsAfter = getBingAccountPoints(self.browser)
            if pointsBefore < pointsAfter:
                del self.googleTrendsShelf[rootTerm]
                return

            # todo
            # if i == (maxRetries / 2):
            #     logging.info("[BING] " + "TIMED OUT GETTING NEW PROXY")
            #     self.webdriver.proxy = self.browser.giveMeProxy()
        print("[BING] Reached max search attempt retries")

        print("Moving passedInTerm to end of list")
        del self.googleTrendsShelf[rootTerm]
        self.googleTrendsShelf[rootTerm] = None


def bingSearches(browser: WebDriver, numberOfSearches: int, isMobile: bool = False):
    """Search Bing"""

    def getRelatedTerms(word: str) -> list:
        """Get related terms"""
        try:
            r = requests.get('https://api.bing.com/osjson.aspx?query=' +
                             word, headers={'User-agent': PC_USER_AGENT})
            return r.json()[1]
        except:
            return []

    def getGoogleTrends(numberOfwords: int) -> list:
        """Get trends"""
        search_terms = []
        i = 0
        while len(search_terms) < numberOfwords:
            i += 1
            r = requests.get('https://trends.google.com/trends/api/dailytrends?hl=' + LANG + '&ed=' + str(
                (date.today() - timedelta(days=i)).strftime('%Y%m%d')) + '&geo=' + GEO + '&ns=15')
            google_trends = json.loads(r.text[6:])
            for topic in google_trends['default']['trendingSearchesDays'][0]['trendingSearches']:
                search_terms.append(topic['title']['query'].lower())
                for related_topic in topic['relatedQueries']:
                    search_terms.append(related_topic['query'].lower())
            search_terms = list(set(search_terms))
        del search_terms[numberOfwords:(len(search_terms) + 1)]
        return search_terms

    def bingSearch(word: str, isMobile: bool):
        """Bing search"""
        try:
            if not isMobile:
                browser.find_element(By.ID, 'sb_form_q').clear()
                time.sleep(1)
            else:
                goToURL(browser, 'https://www.bing.com')
        except:
            goToURL(browser, 'https://www.bing.com')
        time.sleep(2)
        searchbar = browser.find_element(By.ID, 'sb_form_q')
        if FAST or SUPER_FAST:
            searchbar.send_keys(word)
            time.sleep(calculateSleep(1))
        else:
            for char in word:
                searchbar.send_keys(char)
                time.sleep(random.uniform(0.2, 0.45))
        searchbar.submit()
        time.sleep(random.randint(100, 180))
        # Scroll down after the search (adjust the number of scrolls as needed)
        for _ in range(3):  # Scroll down 3 times
            browser.execute_script(
                "window.scrollTo(0, document.body.scrollHeight);"
            )
            time.sleep(random.randint(7, 15)) # Random wait between scrolls
        return getBingAccountPoints(browser)

    global POINTS_COUNTER  # pylint: disable=global-statement
    i = 0
    # try:
    #     words = open("searchwords.txt", "r").read().splitlines()
    #     search_terms = random.sample(words, numberOfSearches)
    #     if search_terms is None:
    #         raise Exception
    # except Exception:
    #     search_terms = getGoogleTrends(numberOfSearches)
    #     if len(search_terms) == 0:
    #         prRed('[ERROR] No search terms found, account skipped.')
    #         finishedAccount()
    #         cleanLogs()
    #         updateLogs()
    #         raise Exception()
    search_terms = getGoogleTrends(numberOfSearches)
    for word in search_terms:
        i += 1
        print(f'[BING] {i}/{numberOfSearches}', end="\r")
        points = bingSearch(word, isMobile)
        if points <= POINTS_COUNTER:
            relatedTerms = getRelatedTerms(word)[:2]
            for term in relatedTerms:
                points = bingSearch(term, isMobile)
                if points >= POINTS_COUNTER:
                    break
        if points > 0:
            POINTS_COUNTER = points
        else:
            break


def locateQuestCard(browser: WebDriver, activity: dict) -> WebElement:
    """Locate rewards card on the page"""
    time.sleep(5)
    all_cards = browser.find_elements(By.CLASS_NAME, "rewards-card-container")
    for card in all_cards:
        data_bi_id = card.get_attribute("data-bi-id")
        if activity["offerId"] == data_bi_id:
            return card
    else:
        raise NoSuchElementException(f"could not locate the provided card: {activity['name']}")
    
def openDailySetActivity(browser: WebDriver, cardId: int):
        # browser.find_element(By.XPATH, f'//*[@id="daily-sets"]/mee-card-group[1]/div/mee-card[{cardId}]/div/card-content/mee-rewards-daily-set-item-content/div/a').click()
        card = browser.execute_script(f'return document.querySelector("mee-rewards-daily-set-section").children[0].querySelector("mee-card-group").children[0].children[{cardId}]')
        card.click()
        time.sleep(2)
        goto_latest_window(browser, time_to_wait=8)
        
def openMorePromotionsActivity(browser: WebDriver, cardId: int):
        # print(f'Current URL Before Clicking: {browser.current_url}')
        # browser.find_element(By.XPATH, f'//*[@id="more-activities"]/div/mee-card[{cardId}]/div/card-content/mee-rewards-more-activities-card-item/div/a').click()
        card  = browser.execute_script(f'return document.querySelector("mee-rewards-more-activities-card").children[0].querySelector("mee-card-group").children[0].children[{cardId}]')
        card.click()
        time.sleep(3)
        # print(f'Current URL After Clicking: {browser.current_url}')
        if re.match(r".*\/welcometour", browser.current_url):
            return
        elif re.match(r".*\/legaltextbox", browser.current_url):
            time.sleep(5)
            if isElementExists(browser, By.XPATH, '//*[@id="modal-host"]/div[2]/button'):
                return
        goto_latest_window(browser, time_to_wait=15)
        

def completeReadToEarn(browser: WebDriver, startingPoints: int):
    print("[READ TO EARN] " + "Trying to complete Read to Earn...")
    client_id = '0000000040170455'
    authorization_base_url = 'https://login.live.com/oauth20_authorize.srf'
    token_url = 'https://login.microsoftonline.com/consumers/oauth2/v2.0/token'
    redirect_uri = ' https://login.live.com/oauth20_desktop.srf'
    scope = [ "service::prod.rewardsplatform.microsoft.com::MBI_SSL"]
    accountName = CURRENT_ACCOUNT
    mobileApp = OAuth2Session(client_id, scope=scope, redirect_uri=redirect_uri)
    authorization_url, state = mobileApp.authorization_url(authorization_base_url, access_type="offline_access", login_hint=accountName)
    # Get Referer URL from webdriver
    goToURL(browser, authorization_url)
    while True:
        print("[READ TO EARN] Waiting for Login")
        if browser.current_url[:48] == "https://login.live.com/oauth20_desktop.srf?code=":
            redirect_response = browser.current_url
            break
        time.sleep(1)
    print("[READ TO EARN] Logged-in successfully !")
    # Use returned URL to create a token
    token = mobileApp.fetch_token(token_url, authorization_response=redirect_response,include_client_id=True)
    
    # json data to confirm an article is read
    json_data = {
        'amount': 1,
        'country': 'us',
        'id': 1,
        'type': 101,
        'attributes': {
            'offerid': 'ENUS_readarticle3_30points',
            },
        }

    balance = startingPoints
    # 10 is the most articles you can read. Sleep time is a guess, not tuned
    for i in range(10):
        # Replace ID with a random value so get credit for a new article
        json_data['id'] = secrets.token_hex(64)
        r = mobileApp.post("https://prod.rewardsplatform.microsoft.com/dapi/me/activities",json=json_data)
        newbalance = r.json().get("response").get("balance")
        if newbalance == balance:
            print("[READ TO EARN] Read All Available Articles !")
            break
        else:
            print("[READ TO EARN] Read Article " + str(i+1))
            balance = newbalance
            time.sleep(calculateSleep(random.randint(10, 20)))
    
    print("[READ TO EARN] Completed the Read to Earn successfully !")
    LOGS[CURRENT_ACCOUNT]['Read to Earn'] = True
    updateLogs()

def completeDailySet(browser: WebDriver):
    """Complete daily set"""

    def completeDailySetSearch():
        """Complete daily set search"""
        time.sleep(2)
        try:
            if browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').is_displayed():
                browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').click()
                return
        except:
            pass
        time.sleep(calculateSleep(15))
        close_all_but_main(browser)
        time.sleep(2)

    def completeDailySetSurvey():
        """Complete daily set survey"""
        time.sleep(calculateSleep(8))
        # Accept cookie popup
        if isElementExists(browser, By.ID, 'bnp_container'):
            browser.find_element(By.ID, 'bnp_btn_accept').click()
            time.sleep(2)
        # Click on later on Bing wallpaper app popup
        if isElementExists(browser, By.ID, 'b_notificationContainer_bop'):
            browser.find_element(By.ID, 'bnp_hfly_cta2').click()
            time.sleep(2)
        waitUntilClickable(browser, By.ID, "btoption0", 15)
        time.sleep(1.5)
        browser.find_element(By.ID, "btoption" +
                             str(random.randint(0, 1))).click()
        time.sleep(calculateSleep(10))
        close_all_but_main(browser)
        time.sleep(2)

    def completeDailySetQuiz():
        """Complete daily set quiz"""
        time.sleep(calculateSleep(12))
        if not waitUntilQuizLoads(browser):
            resetTabs(browser)
            return
        # Accept cookie popup
        if isElementExists(browser, By.ID, 'bnp_container'):
            browser.find_element(By.ID, 'bnp_btn_accept').click()
            time.sleep(2)
        browser.find_element(By.XPATH, '//*[@id="rqStartQuiz"]').click()
        waitUntilVisible(browser, By.XPATH,
                         '//*[@id="currentQuestionContainer"]/div/div[1]', 10)
        time.sleep(3)
        numberOfQuestions = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.maxQuestions")
        numberOfOptions = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.numberOfOptions")
        for _ in range(numberOfQuestions):
            if numberOfOptions == 8:
                answers = []
                for i in range(8):
                    if browser.find_element(By.ID, "rqAnswerOption" + str(i)).get_attribute(
                            "iscorrectoption").lower() == "true":
                        answers.append("rqAnswerOption" + str(i))
                for answer in answers:
                    # Click on later on Bing wallpaper app popup
                    if isElementExists(browser, By.ID, 'b_notificationContainer_bop'):
                        browser.find_element(By.ID, 'bnp_hfly_cta2').click()
                        time.sleep(2)
                    waitUntilClickable(browser, By.ID, answer, 25)
                    browser.find_element(By.ID, answer).click()
                    time.sleep(calculateSleep(random.randint(10, 15)))
                    if not waitUntilQuestionRefresh(browser):
                        return
                time.sleep(calculateSleep(6))
            elif numberOfOptions in [2, 3, 4]:
                correctOption = browser.execute_script(
                    "return _w.rewardsQuizRenderInfo.correctAnswer")
                for i in range(4):
                    if browser.find_element(By.ID, "rqAnswerOption" + str(i)).get_attribute(
                            "data-option") == correctOption:
                        # Click on later on Bing wallpaper app popup
                        if isElementExists(browser, By.ID, 'b_notificationContainer_bop'):
                            browser.find_element(
                                By.ID, 'bnp_hfly_cta2').click()
                            time.sleep(2)
                        waitUntilClickable(
                            browser, By.ID, f"rqAnswerOption{str(i)}", 25)
                        browser.find_element(
                            By.ID, "rqAnswerOption" + str(i)).click()
                        time.sleep(calculateSleep(random.randint(10, 15)))
                        if not waitUntilQuestionRefresh(browser):
                            return
                        break
                time.sleep(calculateSleep(6))
        time.sleep(calculateSleep(6))
        close_all_but_main(browser)
        time.sleep(2)

    def completeDailySetVariableActivity():
        """Complete daily set variable activity"""
        time.sleep(calculateSleep(10))
        # Accept cookie popup
        if isElementExists(browser, By.ID, 'bnp_container'):
            browser.find_element(By.ID, 'bnp_btn_accept').click()
            time.sleep(2)
        try:
            browser.find_element(By.XPATH, '//*[@id="rqStartQuiz"]').click()
            waitUntilVisible(
                browser, By.XPATH, '//*[@id="currentQuestionContainer"]/div/div[1]', 3)
        except (NoSuchElementException, TimeoutException):
            try:
                counter = str(
                    browser.find_element(By.XPATH, '//*[@id="QuestionPane0"]/div[2]').get_attribute('innerHTML'))[
                    :-1][1:]
                numberOfQuestions = max(
                    [int(s) for s in counter.split() if s.isdigit()])
                for question in range(numberOfQuestions):
                    # Click on later on Bing wallpaper app popup
                    if isElementExists(browser, By.ID, 'b_notificationContainer_bop'):
                        browser.find_element(By.ID, 'bnp_hfly_cta2').click()
                        time.sleep(2)

                    browser.execute_script(
                f'document.evaluate("//*[@id=\'QuestionPane{str(question)}\']/div[1]/div[2]/a[{str(random.randint(1, 3))}]/div", document, null, XPathResult.FIRST_ORDERED_NODE_TYPE, null).singleNodeValue.click()')
                    time.sleep(random.randint(10, 15))
                time.sleep(5)
                close_all_but_main(browser)
                time.sleep(2)
                return
            except NoSuchElementException:
                time.sleep(calculateSleep(random.randint(5, 9)))
                close_all_but_main(browser)
                time.sleep(2)
                return
        time.sleep(3)
        correctAnswer = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.correctAnswer")
        if browser.find_element(By.ID, "rqAnswerOption0").get_attribute("data-option") == correctAnswer:
            browser.find_element(By.ID, "rqAnswerOption0").click()
        else:
            browser.find_element(By.ID, "rqAnswerOption1").click()
        time.sleep(10)
        close_all_but_main(browser)
        time.sleep(2)

    def completeDailySetThisOrThat():
        """Complete daily set this or that"""
        time.sleep(calculateSleep(25))
        # Accept cookie popup
        if isElementExists(browser, By.ID, 'bnp_container'):
            browser.find_element(By.ID, 'bnp_btn_accept').click()
            time.sleep(2)
        if not waitUntilQuizLoads(browser):
            resetTabs(browser)
            return
        browser.find_element(By.XPATH, '//*[@id="rqStartQuiz"]').click()
        waitUntilVisible(browser, By.XPATH,
                         '//*[@id="currentQuestionContainer"]/div/div[1]', 15)
        time.sleep(5)
        for _ in range(10):
            # Click on later on Bing wallpaper app popup
            if isElementExists(browser, By.ID, 'b_notificationContainer_bop'):
                browser.find_element(By.ID, 'bnp_hfly_cta2').click()
                time.sleep(2)

            answerEncodeKey = browser.execute_script("return _G.IG")
            waitUntilVisible(browser, By.ID, "rqAnswerOption0", 15)
            answer1 = browser.find_element(By.ID, "rqAnswerOption0")
            answer1Title = answer1.get_attribute('data-option')
            answer1Code = getAnswerCode(answerEncodeKey, answer1Title)

            answer2 = browser.find_element(By.ID, "rqAnswerOption1")
            answer2Title = answer2.get_attribute('data-option')
            answer2Code = getAnswerCode(answerEncodeKey, answer2Title)

            correctAnswerCode = browser.execute_script(
                "return _w.rewardsQuizRenderInfo.correctAnswer")

            waitUntilClickable(browser, By.ID, "rqAnswerOption0", 25)
            if answer1Code == correctAnswerCode:
                answer1.click()
                time.sleep(calculateSleep(25))
            elif answer2Code == correctAnswerCode:
                answer2.click()
                time.sleep(calculateSleep(25))

        time.sleep(calculateSleep(6))
        close_all_but_main(browser)
        time.sleep(2)

    print('[DAILY SET]', 'Trying to complete the Daily Set...')
    d = getDashboardData(browser)
    error = False
    todayDate = datetime.today().strftime('%m/%d/%Y')
    todayPack = []
    i = 0
    for date_, data in d['dailySetPromotions'].items():
        if date_ == todayDate:
            todayPack = data
    for activity in todayPack:
        try:
            if not activity['complete']:
                # cardNumber = int(activity['offerId'][-1:])
                cardNumber = i
                openDailySetActivity(browser, cardId=cardNumber)
                print(f'Card Name: {activity["title"]}')
                if activity['promotionType'] == "urlreward":
                    if "poll" in activity['title']:
                        searchUrl = urllib.parse.unquote(
                            urllib.parse.parse_qs(urllib.parse.urlparse(activity['destinationUrl']).query)['ru'][0])
                        searchUrlQueries = urllib.parse.parse_qs(
                            urllib.parse.urlparse(searchUrl).query)
                        filters = {}
                        for filter in searchUrlQueries['filters'][0].split(" "):
                            filter = filter.split(':', 1)
                            filters[filter[0]] = filter[1]
                        if "PollScenarioId" in filters:
                            print(
                                '[DAILY SET]', 'Completing poll of card ' + str(cardNumber))
                            completeDailySetSurvey()
                    else:
                        print('[DAILY SET]',
                                'Completing search of card ' + str(cardNumber))
                        completeDailySetSearch()
                if activity['promotionType'] == "quiz":
                    if activity['pointProgressMax'] == 50 and activity['pointProgress'] == 0:
                        print(
                            '[DAILY SET]', 'Completing This or That of card ' + str(cardNumber))
                        completeDailySetThisOrThat()
                    elif (activity['pointProgressMax'] == 40 or activity['pointProgressMax'] == 30) and activity['pointProgress'] == 0:
                        print('[DAILY SET]',
                                'Completing quiz of card ' + str(cardNumber))
                        completeDailySetQuiz()
                    elif activity['pointProgressMax'] == 10 and activity['pointProgress'] == 0:
                        searchUrl = urllib.parse.unquote(
                            urllib.parse.parse_qs(urllib.parse.urlparse(activity['destinationUrl']).query)['ru'][0])
                        searchUrlQueries = urllib.parse.parse_qs(
                            urllib.parse.urlparse(searchUrl).query)
                        filters = {}
                        for filter in searchUrlQueries['filters'][0].split(" "):
                            filter = filter.split(':', 1)
                            filters[filter[0]] = filter[1]
                        if "PollScenarioId" in filters:
                            print(
                                '[DAILY SET]', 'Completing poll of card ' + str(cardNumber))
                            completeDailySetSurvey()
                        else:
                            print(
                                '[DAILY SET]', 'Completing quiz of card ' + str(cardNumber))
                            completeDailySetVariableActivity()
        except Exception as exc:
            displayError(exc)
            error = True
            resetTabs(browser)
    if not error:
        prGreen("[DAILY SET] Completed the Daily Set successfully !")
    else:
        prYellow(
            "[DAILY SET] Daily Set did not completed successfully ! Streak not increased")
    LOGS[CURRENT_ACCOUNT]['Daily'] = True
    updateLogs()


def completePunchCards(browser: WebDriver):
    """Complete punch cards"""

    def completePunchCard(url: str, childPromotions: dict):
        """complete punch card"""
        goToURL(browser, url)
        for child in childPromotions:
            if not child['complete']:
                # print(f"Punch Card Name: {child['name']}")
                if child['promotionType'] == "urlreward":
                    # print(f"Offer Title: {child['attributes']['title']}")
                    browser.find_element(By.XPATH, "//a[@class='offer-cta']/div").click()
                    goto_latest_window(browser, random.randint(13, 17))
                    time.sleep(calculateSleep(7))
                    close_all_but_main(browser)
                    time.sleep(2)
                if child['promotionType'] == "quiz" and child['pointProgressMax'] >= 50:
                    # print(f"Offer Title: {child['attributes']['title']}")
                    browser.find_element(By.XPATH,
                                            '//*[@id="rewards-dashboard-punchcard-details"]/div[2]/div[2]/div[7]/div[3]/div[1]/a').click()
                    goto_latest_window(browser, random.randint(13, 17))
                    time.sleep(calculateSleep(15))
                    try:
                        waitUntilVisible(browser, By.ID, "rqStartQuiz", 15)
                        browser.find_element(By.ID, "rqStartQuiz").click()
                    except:
                        pass
                    time.sleep(calculateSleep(6))
                    waitUntilVisible(
                        browser, By.ID, "currentQuestionContainer", 15)
                    numberOfQuestions = browser.execute_script(
                        "return _w.rewardsQuizRenderInfo.maxQuestions")
                    AnswerdQuestions = browser.execute_script(
                        "return _w.rewardsQuizRenderInfo.CorrectlyAnsweredQuestionCount")
                    numberOfQuestions -= AnswerdQuestions
                    for question in range(numberOfQuestions):
                        answer = browser.execute_script(
                            "return _w.rewardsQuizRenderInfo.correctAnswer")
                        waitUntilClickable(
                            browser, By.XPATH, f'//input[@value="{answer}"]', 25)
                        browser.find_element(
                            By.XPATH, f'//input[@value="{answer}"]').click()
                        time.sleep(calculateSleep(25))
                    time.sleep(5)
                    close_all_but_main(browser)
                    browser.refresh()
                    break
                elif child['promotionType'] == "quiz" and child['pointProgressMax'] < 50:
                    # print(f"Offer Title: {child['attributes']['title']}")
                    browser.find_element(By.XPATH, "//a[@class='offer-cta']/div").click()
                    time.sleep(1)
                    goto_latest_window(browser, random.randint(13, 17))
                    time.sleep(calculateSleep(8))
                    waitUntilVisible(browser, By.XPATH,
                                        '//*[@id="QuestionPane0"]/div[2]', 15)
                    counter = str(
                        browser.find_element(By.XPATH, '//*[@id="QuestionPane0"]/div[2]').get_attribute('innerHTML'))[
                        :-1][1:]
                    numberOfQuestions = max(
                        [int(s) for s in counter.split() if s.isdigit()])
                    for question in range(numberOfQuestions):
                        browser.find_element(By.XPATH,f'//*[@id="QuestionPane{question}"]/div[1]/div[2]/a[{random.randint(1, 3)}]/div').click()
                        time.sleep(random.randint(100, 700) / 100)
                        browser.find_element(By.XPATH,f'//*[@id="AnswerPane{question}"]/div[1]/div[2]/div[4]/a/div/span/input').click()
                        time.sleep(random.randint(100, 700) / 100)
                    time.sleep(5)
                    close_all_but_main(browser)
                    time.sleep(2)
                    browser.refresh()
                    break

    print('[PUNCH CARDS]', 'Trying to complete the Punch Cards...')
    punchCards = getDashboardData(browser)['punchCards']
    for punchCard in punchCards:
        try:
            if (
                    punchCard['parentPromotion'] is not None and punchCard['childPromotions'] is not None and
                    punchCard['parentPromotion']['complete'] is False and
                    punchCard['parentPromotion']['pointProgressMax'] != 0
            ):
                url = punchCard['parentPromotion']['attributes']['destination']
                # print(f"PunchCards Name: {punchCard['parentPromotion']['name']}")
                completePunchCard(url, punchCard['childPromotions'])
        except Exception as exc:
            displayError(exc)
            resetTabs(browser)
    time.sleep(2)
    goToURL(browser, BASE_URL)
    time.sleep(2)
    LOGS[CURRENT_ACCOUNT]['Punch cards'] = True
    updateLogs()
    prGreen('[PUNCH CARDS] Completed the Punch Cards successfully !')


def completeMorePromotions(browser: WebDriver):
    """Complete more promotions"""

    def completeMorePromotionWelcometour():
        """Complete more promotion Welcometour"""
        # card = locateQuestCard(browser, _activity)
        # card.click()
        time.sleep(7)
        if "https://rewards.microsoft.com/welcometour" or "https://rewards.bing.com/welcometour" in browser.current_url:
            browser.execute_script("""
                var welcometourPane = document.getElementsByClassName("welcome-tour-modal")[0];
                const sleep = (ms) => new Promise(resolve => setTimeout(resolve, ms));
                async function completeWelcomeTour() {
                    let wtslides = welcometourPane.children.length;
                    for (let i = 0; i <= wtslides; i++) {
                        let wtslide = welcometourPane.children[i];
                        if (i != wtslides-1){
                            var nexbutton = wtslide?.getElementsByClassName("next-button")[0];
                        } else {
                            nexbutton = wtslide?.querySelector("#claim-button");
                        }
                        if (wtslide.offsetWidth != 0 && wtslide.offsetHeight != 0){
                            nexbutton.click();
                            await sleep(3000);
                        }
                    }
                };
                completeWelcomeTour();
            """)
            time.sleep(7)
        if re.match(r".*\/\?pin.*", browser.current_url):
            goToURL(browser, BASE_URL)
            time.sleep(2)

    def completeMorePromotionSearch():
        """Complete more promotion search"""
        time.sleep(2.5)
        try:
            if browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').is_displayed():
                browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').click()
                return
        except:
            pass
        time.sleep(calculateSleep(15))
        close_all_but_main(browser)
        time.sleep(2)

    def completeMorePromotionQuiz():
        """Complete more promotion quiz"""
        time.sleep(calculateSleep(10))
        if not waitUntilQuizLoads(browser):
            resetTabs(browser)
            return
        CurrentQuestionNumber = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.currentQuestionNumber")
        if CurrentQuestionNumber == 1 and isElementExists(browser, By.XPATH, '//*[@id="rqStartQuiz"]'):
            browser.find_element(By.XPATH, '//*[@id="rqStartQuiz"]').click()
        waitUntilVisible(browser, By.XPATH,
                         '//*[@id="currentQuestionContainer"]/div/div[1]', 15)
        time.sleep(3)
        numberOfQuestions = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.maxQuestions")
        Questions = numberOfQuestions - CurrentQuestionNumber + 1
        numberOfOptions = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.numberOfOptions")
        for _ in range(Questions):
            if numberOfOptions == 8:
                answers = []
                for i in range(8):
                    if browser.find_element(By.ID, "rqAnswerOption" + str(i)).get_attribute(
                            "iscorrectoption").lower() == "true":
                        answers.append("rqAnswerOption" + str(i))
                for answer in answers:
                    waitUntilClickable(browser, By.ID, answer, 25)
                    browser.find_element(By.ID, answer).click()
                    time.sleep(calculateSleep(random.randint(5, 9)))
                    if not waitUntilQuestionRefresh(browser):
                        return
                time.sleep(calculateSleep(6))
            elif numberOfOptions in [2, 3, 4]:
                correctOption = browser.execute_script(
                    "return _w.rewardsQuizRenderInfo.correctAnswer")
                for i in range(4):
                    if browser.find_element(By.ID, f"rqAnswerOption{str(i)}").get_attribute(
                            "data-option") == correctOption:
                        waitUntilClickable(
                            browser, By.ID, f"rqAnswerOption{str(i)}", 25)
                        browser.find_element(
                            By.ID, f"rqAnswerOption{str(i)}").click()
                        time.sleep(random.randint(10, 15))
                        if not waitUntilQuestionRefresh(browser):
                            return
                        break
                time.sleep(random.randint(5, 9))
        time.sleep(random.randint(5, 9))
        close_all_but_main(browser)
        time.sleep(2)

    def completeMorePromotionABC():
        """Complete more promotion ABC"""
        time.sleep(calculateSleep(random.randint(10, 15)))
        waitUntilVisible(browser, By.XPATH,
                         '//*[@id="QuestionPane0"]/div[2]', 15)
        counter = str(browser.find_element(By.XPATH, '//*[@id="QuestionPane0"]/div[2]').get_attribute('innerHTML'))[
            :-1][1:]
        numberOfQuestions = max([int(s)
                                for s in counter.split() if s.isdigit()])
        for question in range(numberOfQuestions):
            browser.execute_script(
                f'document.evaluate("//*[@id=\'QuestionPane{str(question)}\']/div[1]/div[2]/a[{str(random.randint(1, 3))}]/div", document, null, XPathResult.FIRST_ORDERED_NODE_TYPE, null).singleNodeValue.click()')
            time.sleep(random.randint(10, 15))
        time.sleep(random.randint(5, 9))
        close_all_but_main(browser)
        time.sleep(2)

    def completeMorePromotionThisOrThat():
        """Complete more promotion this or that"""
        time.sleep(calculateSleep(8))
        if not waitUntilQuizLoads(browser):
            resetTabs(browser)
            return
        CrrentQuestionNumber = browser.execute_script(
            "return _w.rewardsQuizRenderInfo.currentQuestionNumber")
        NumberOfQuestionsLeft = 10 - CrrentQuestionNumber + 1
        if CrrentQuestionNumber == 1 and isElementExists(browser, By.XPATH, '//*[@id="rqStartQuiz"]'):
            browser.find_element(By.XPATH, '//*[@id="rqStartQuiz"]').click()
        waitUntilVisible(browser, By.XPATH,
                         '//*[@id="currentQuestionContainer"]/div/div[1]', 10)
        time.sleep(3)
        for _ in range(NumberOfQuestionsLeft):
            answerEncodeKey = browser.execute_script("return _G.IG")

            waitUntilVisible(browser, By.ID, "rqAnswerOption0", 15)
            answer1 = browser.find_element(By.ID, "rqAnswerOption0")
            answer1Title = answer1.get_attribute('data-option')
            answer1Code = getAnswerCode(answerEncodeKey, answer1Title)

            answer2 = browser.find_element(By.ID, "rqAnswerOption1")
            answer2Title = answer2.get_attribute('data-option')
            answer2Code = getAnswerCode(answerEncodeKey, answer2Title)

            correctAnswerCode = browser.execute_script(
                "return _w.rewardsQuizRenderInfo.correctAnswer")

            waitUntilClickable(browser, By.ID, "rqAnswerOption0", 15)
            if answer1Code == correctAnswerCode:
                answer1.click()
                time.sleep(calculateSleep(random.randint(15, 20)))

            elif answer2Code == correctAnswerCode:
                answer2.click()
                time.sleep(calculateSleep(random.randint(15, 20)))

        time.sleep(random.randint(5, 9))
        close_all_but_main(browser)
        time.sleep(2)

    def completePromotionalItems():
        """Complete promotional items"""
        try:
            # print("Doing Banner Items")
            item: list[dict] = getDashboardData(browser)["promotionalItem"]
            if (item["pointProgressMax"] == 100 or item["pointProgressMax"] == 200) and item["complete"] is False and \
                    item["destinationUrl"] == BASE_URL:
                browser.find_element(
                    By.XPATH, '//*[@id="promo-item"]/section/div/div/div/span').click()
                time.sleep(8)
                if re.match(r".*\/legaltextbox", browser.current_url):
                    time.sleep(5)
                    if isElementExists(browser, By.XPATH, '//*[@id="modal-host"]/div[2]/button'):
                        # print("Clicking Close Dialog")
                        browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').click()
                        return
                goto_latest_window(browser)
                time.sleep(calculateSleep(8))
                close_all_but_main(browser)
                time.sleep(2)
        except Exception as exc:
            displayError(exc)

    print('[MORE PROMO]', 'Trying to complete More Promotions...')
    morePromotions: list[dict] = getDashboardData(browser)['morePromotions']
    i = 0
    for promotion in morePromotions:
        try:
            promotionTitle = promotion["title"]
            # print(f"promotionTitle={promotionTitle}")
            if (promotion["complete"] is not False or promotion["pointProgressMax"] == 0):
                continue
            if "Mid-week puzzle" in promotionTitle:
                print(
                    "Mid-week puzzle found",
                    "MS-Rewards-Farmer detected mid-week puzzle activity, which isn't supported."
                    " Please manually complete",
                )
                continue
            if promotion["exclusiveLockedFeatureStatus"] == "locked":
                continue
            print(f"promotionTitle={promotionTitle}")
            openMorePromotionsActivity(browser, cardId=i)
            i += 1
            if re.match(r".*\/legaltextbox", browser.current_url):
                time.sleep(5)
                if isElementExists(browser, By.XPATH, '//*[@id="modal-host"]/div[2]/button'):
                    # print("Clicking Close Dialog")
                    browser.find_element(By.XPATH, '//*[@id="modal-host"]/div[2]/button').click()
                    continue
            if "Search the lyrics of a song" in promotionTitle:
                    goToURL(browser, "https://www.bing.com/search?q=black+sabbath+supernaut+lyrics")
                    time.sleep(8)
                    close_all_but_main(browser)
            elif "Translate anything" in promotionTitle:
                goToURL(browser, "https://www.bing.com/search?q=translate+pencil+sharpener+to+spanish")
                time.sleep(8)
                close_all_but_main(browser)
            elif "Discover open job roles" in promotionTitle:
                goToURL(browser, "https://www.bing.com/search?q=walmart+open+job+roles")
                time.sleep(8)
                close_all_but_main(browser)
            elif "Plan a quick getaway" in promotionTitle:
                goToURL(browser, "https://www.bing.com/search?q=flights+nyc+to+paris")
                time.sleep(8)
                close_all_but_main(browser)
            elif "You can track your package" in promotionTitle:
                waitUntilClickable(
                    browser, By.ID, "sb_form_q", time_to_wait=20
                )
                searchbar = browser.find_element(By.ID, "sb_form_q")
                searchbar.click()
                searchbar.send_keys("usps tracking")
                searchbar.submit()

                time.sleep(8)
                close_all_but_main(browser)
            elif "Find somewhere new to explore" in promotionTitle:
                goToURL(browser, 
                    "https://www.bing.com/search?q=directions+to+new+york"
                )
                time.sleep(8)
                close_all_but_main(browser)
            elif "Too tired to cook tonight?" in promotionTitle:
                waitUntilClickable(
                    browser, By.ID, "sb_form_q", time_to_wait=20
                )
                searchbar = browser.find_element(By.ID, "sb_form_q")
                searchbar.click()
                searchbar.send_keys("pizza delivery near me")
                searchbar.submit()

                time.sleep(8)
                close_all_but_main(browser)
            elif "Prepare for the weather​" in promotionTitle:
                waitUntilClickable(
                    browser, By.ID, "sb_form_q", time_to_wait=20
                )
                searchbar = browser.find_element(By.ID, "sb_form_q")
                searchbar.click()
                searchbar.send_keys("upcoming weather")
                searchbar.submit()

                time.sleep(8)
                close_all_but_main(browser)
            elif "Quickly convert your money" in promotionTitle:
                waitUntilClickable(
                    browser, By.ID, "sb_form_q", time_to_wait=20
                )
                searchbar = browser.find_element(By.ID, "sb_form_q")
                searchbar.click()
                searchbar.send_keys("convert 374 usd to yen")
                searchbar.submit()

                time.sleep(8)
                close_all_but_main(browser)
            elif "Learn to cook a new recipe" in promotionTitle:
                waitUntilClickable(
                    browser, By.ID, "sb_form_q", time_to_wait=20
                )
                searchbar = browser.find_element(By.ID, "sb_form_q")
                searchbar.click()
                searchbar.send_keys("how cook pierogi")
                searchbar.submit()

                time.sleep(8)
                close_all_but_main(browser)
            elif promotion['promotionType'] == "welcometour":
                completeMorePromotionWelcometour()
            elif promotion['promotionType'] == "urlreward" or promotion['promotionType'] == "":
                # print("Trying URLREWARD....")
                completeMorePromotionSearch()
            elif promotion['promotionType'] == "quiz":
                # print("Trying Quiz....")
                if promotion['pointProgressMax'] == 10:
                    # print("Trying Quiz 10 pts....")
                    completeMorePromotionABC()
                elif promotion['pointProgressMax'] == 30 or promotion['pointProgressMax'] == 40:
                    # print("Trying Quiz 30 40 pts....")
                    completeMorePromotionQuiz()
                elif promotion['pointProgressMax'] == 50:
                    # print("Trying Quiz 50 pts....")
                    completeMorePromotionThisOrThat()
            else:
                if promotion['pointProgressMax'] == 100 or promotion['pointProgressMax'] == 200:
                    # print("Trying Quiz 100 pts....")
                    completeMorePromotionSearch()
            if promotion['complete'] is False and promotion['pointProgressMax'] == 100 and promotion[
                'promotionType'] == "" and promotion['destinationUrl'] == BASE_URL:
                completeMorePromotionSearch()
        except Exception as exc:
            displayError(exc)
            resetTabs(browser)

    completePromotionalItems()
    LOGS[CURRENT_ACCOUNT]['More promotions'] = True
    updateLogs()
    prGreen('[MORE PROMO] Completed More Promotions successfully !')


def completeMSNShoppingGame(browser: WebDriver , email: str) -> bool:
    """Complete MSN Shopping Game, returns True if completed successfully else False"""

    def expandShadowElement(element, index: int = None) -> Union[List[WebElement], WebElement]:
        """Returns childrens of shadow element"""
        if index is not None:
            shadow_root = WebDriverWait(browser, 45).until(
                ec.visibility_of(browser.execute_script(
                    'return arguments[0].shadowRoot.children', element)[index])
            )
        else:
            # wait to visible one element then get the list
            WebDriverWait(browser, 45).until(
                ec.visibility_of(browser.execute_script(
                    'return arguments[0].shadowRoot.children', element)[0])
            )
            shadow_root = browser.execute_script(
                'return arguments[0].shadowRoot.children', element)
        return shadow_root

    def getChildren(element) -> List[WebElement]:
        """get children"""
        children = browser.execute_script(
            'return arguments[0].children', element)
        return children

    def getSignInButton() -> WebElement:
        """check whether user is signed in or not and return the button to sign in"""
        script_to_user_pref_container = 'document.getElementsByTagName("shopping-page-base")[0]\
            .shadowRoot.children[0].children[1].children[0]\
            .shadowRoot.children[0].shadowRoot.children[0]\
            .getElementsByClassName("user-pref-container")[0]'
        WebDriverWait(browser, 60).until(ec.visibility_of(
            browser.execute_script(f'return {script_to_user_pref_container}')
        )
        )
        button = WebDriverWait(browser, 60).until(ec.visibility_of(
            browser.execute_script(
                f'return {script_to_user_pref_container}.\
                    children[0].children[0].shadowRoot.children[0].\
                    getElementsByClassName("me-control")[0]'
            )
        )
        )
        return button

    def signIn() -> None:
        """sign in"""
        sign_in_button = getSignInButton()
        sign_in_button.click()
        print("[MSN GAME] Signing in...")
        time.sleep(5)
        waitUntilVisible(browser, By.ID, 'i0116', 10)
        browser.find_element(By.ID, 'i0116').send_keys(email)
        browser.find_element(By.ID, 'idSIButton9').click()
        waitUntilVisible(browser, By.TAG_NAME, 'shopping-page-base', 60)
        expandShadowElement(browser.find_element(
            By.TAG_NAME, 'shopping-page-base'), 0)
        time.sleep(5)
        getSignInButton()
        time.sleep(5)

    def getGamingCard() -> Union[WebElement, Literal[False]]:
        """get gaming card, if completed before raises GamingCardIsNotActive exception"""
        shopping_page_base_childs = expandShadowElement(browser.find_element(By.TAG_NAME, 'shopping-page-base'), 0)
        shopping_homepage = shopping_page_base_childs.find_element(By.TAG_NAME, 'shopping-homepage')
        cs_feed_layout = expandShadowElement(expandShadowElement(shopping_homepage, 0).find_element(By.TAG_NAME, 'cs-feed-layout'))
        for element in cs_feed_layout:
            if element.get_attribute("gamestate") == "active":
                if (browser.execute_script(
                        "if (arguments[0]?.shadowRoot.querySelector('msft-stripe')) {return true} else {return false};", element)):
                            return element
            elif element.get_attribute("gamestate") == "idle":
                if (browser.execute_script(
                        "if (arguments[0]?.shadowRoot.querySelector('msft-stripe')) {return true} else {return false};", element)):
                            return element
                # raise GamingCardIsNotActive
        else:
            return False

    def setup_msnShoppingGame():
        try:
            browser.execute_script(
                """
                var msnShoppingGamePane = document.querySelector("shopping-page-base")?.shadowRoot.querySelector("shopping-homepage")?.shadowRoot.querySelector("cs-feed-layout")?.shadowRoot.querySelector("msn-shopping-game-pane");

                var msftFeedLayout = document.querySelector("shopping-page-base")
                    ?.shadowRoot.querySelector("shopping-homepage")
                    ?.shadowRoot.querySelector("cs-feed-layout");

                var tok = localStorage.getItem("1s-tokens");
                var msntoken = JSON.parse(tok).accessToken;


                function modifyGameProducts(){
                    msnShoppingGamePane.displayedShoppingEntities = [msnShoppingGamePane.displayedShoppingEntities[0]];
                }


                function removeDailyGameLimit(){
                    if(msnShoppingGamePane.displayedShoppingEntities.length > 1) 
                        modifyGameProducts();

                    localStorage.removeItem("gamesPerDay");
                    msnShoppingGamePane.dailyLimitReached = false;
                    if(msnShoppingGamePane.leaderboardRecord)
                        msnShoppingGamePane.leaderboardRecord.dailyGuessingGamesPlayed = 0;
                    
                    msnShoppingGamePane.gameState = (msnShoppingGamePane.gameState == "idle" ? "active" : msnShoppingGamePane.gameState);
                }

                function createButtonElement(){
                    if(!window.elementsCreated) 
                        window.elementsCreated = 0;
                    var divElem = document.createElement("div");
                    divElem.className = "view-leaderboard stats-game-counter";
                    divElem.style = `right: unset; left: ${25+(window.elementsCreated++ * 100)}px; font-size: 13px;background: linear-gradient(100.25deg, rgba(7, 158, 130, 0.9) 0%, rgba(2, 100, 188, 0.9) 100%);color: white;font-weight: 700;`;
                    var parentElem = msnShoppingGamePane.gameContainerRef.getElementsByClassName("game-panel-container")[0];
                    parentElem.appendChild(divElem);
                    return divElem;
                }


                function incrementGameCounter(){
                    if(!window.gameCounterElem){
                        window.gameCounter = 0;
                        window.gameCounterElem = createButtonElement();
                    }
                    window.gameCounter++;
                    window.gameCounterElem.textContent = `Game: ${window.gameCounter}`;
                }

                async function reportActivity(){
                    return await fetch("https://assets.msn.com/service/news/feed/segments/shopping?ocid=shopping-shophp-Peregrine&apikey=Xr2pbC1j5NMUwFF5YHTlhDDkcftEafmPoVP3pfA5eZ&timeOut=10000&cm="+MeControl.Config.mkt.toLowerCase()+"&scn=MSNRPSAuth&$select=rewards|reportactivity|guessinggame|0|"+window.gameHash+"&$filter=~5000&t="+Date.now().toString(),{
                        method: "GET",
                        cache: "no-store",
                        headers: {'Authorization': `Bearer ${msntoken}`}
                    });
                }


                async function modifyGame(){
                    // Get the game hash.
                    
                    window.gameHash = msnShoppingGamePane.displayedShoppingEntities[0].gameHash;
                    
                    // Check if the shopping game was found.
                    if(msnShoppingGamePane != null)
                    {		
                        // Switches msnShoppingGamePane slot with slot2, bringing it to the top of the page.
                        if(msnShoppingGamePane.style.gridArea != "slot2"){
                            msftFeedLayout.shadowRoot.children[1].style.gridArea = msnShoppingGamePane.style.gridArea;
                            msnShoppingGamePane.style.gridArea = "slot2";

                            // Scroll to the top of the page, For people who scroll down before running the script.
                            msnShoppingGamePane.scrollIntoView({ behavior: "smooth" });
                        }
                        
                        // Keep the game at the top when layout changes.
                        if(!window.layoutColumnsChangedOG){
                            window.layoutColumnsChangedOG = msnShoppingGamePane.layoutColumnsChanged;
                            msnShoppingGamePane.layoutColumnsChanged = function(e, t){
                                layoutColumnsChangedOG.call(msnShoppingGamePane, [e, t]);
                                msnShoppingGamePane.style.gridArea = "slot2";
                            }
                        }
                        
                        // Override their 'startCountdown' so we can increment the game count.
                        if(!window.startCountdownOG){
                            window.startCountdownOG = msnShoppingGamePane.startCountdown;
                            msnShoppingGamePane.startCountdown = function(){
                                window.startCountdownOG.call(msnShoppingGamePane);
                                setTimeout(() => {
                                    incrementGameCounter();
                                    modifyGameProducts();
                                }, (msnShoppingGamePane.gameSettings.newGameCountdown * 1000) + 1200);
                            }
                        }
                        
                        // Override their gSCS to always return green.
                        msnShoppingGamePane.gSCS = function (e) {
                            return msnShoppingGamePane.isGameFinished ? "--price-color:#00AE56;--price-color-dark:#00AE56" : "";
                        }
                        
                        // Override their 'getGameResult' function with our own to execute 'autoReplay' and 'updateUserPointsBalance' on game complete, Also removes the 10 game limit.
                        msnShoppingGamePane.getGameResult = async function(e) 
                        {
                            // Make sure a product card is selected.
                            if (msnShoppingGamePane.isGameFinished)
                            {
                                // Change current gameState to 'win'.
                                msnShoppingGamePane.gameState = 'win';

                                // Remove daily game limit.
                                removeDailyGameLimit();

                                // Report 'guessinggame' activity, Only calling when the answer was wrong.
                                if(msnShoppingGamePane.selectedCardIndex != msnShoppingGamePane.c_ai && msnShoppingGamePane.selectedCardIndex > -1){
                                    msnShoppingGamePane.gameContainerRef.querySelector("fluent-card").parentElement.style = "border:4px solid rgb(0, 174, 86)";
                                    msnShoppingGamePane.selectedCardIndex = -1;
                                    msnShoppingGamePane.confettiAnimate.play();
                                    await reportActivity();				
                                }
                                
                                // Automatically click 'Play Again'.
                                if(msnShoppingGamePane.selectedCardIndex > -1){
                                    msnShoppingGamePane.selectedCardIndex = -1;
                                    setTimeout(()=>Array.from(msnShoppingGamePane.gameContainerRef.querySelectorAll("button")).find(e=>e.textContent.toLowerCase().includes("play again"))?.click(), 25);
                                }
                                return "win";
                            }
                        };
                        setInterval(removeDailyGameLimit, 100);
                        incrementGameCounter();

                    }
                };

                setTimeout(async () => {modifyGame(); }, 500);
                """)
        except:
            pass

    def clickAnswer() -> None:
        """click answer"""
        options_container = expandShadowElement(gaming_card, 1)
        options_elements = getChildren(getChildren(options_container)[1])
        # click on the correct answer in options_elements
        correct_answer = options_elements[int(0)]
        WebDriverWait(browser, 10).until(ec.element_to_be_clickable(correct_answer))
        correct_answer.click()
        # click 'select' button
        select_button = correct_answer.find_element(
            By.CLASS_NAME, 'shopping-select-overlay-button')
        WebDriverWait(browser, 7).until(
            ec.element_to_be_clickable(select_button))
        select_button.click()

    def clickPlayAgain() -> None:
        """click play again"""
        time.sleep(random.randint(4, 6))
        options_container = expandShadowElement(gaming_card)[1]
        getChildren(options_container)[0].find_element(
            By.TAG_NAME, 'button').click()
        
    def isGamingCardFinished() -> bool:
        """checkes if game is finished"""
        try:
            msn_shopping_game_pane = browser.execute_script('return document.querySelector("shopping-page-base")?.shadowRoot.querySelector("shopping-homepage")?.shadowRoot.querySelector("cs-feed-layout")?.shadowRoot.querySelector("msn-shopping-game-pane")')
            WebDriverWait(browser, 15).until(ec.visibility_of(msn_shopping_game_pane))
            time.sleep(7)
            if 'tomorrow' in (browser.execute_script('return arguments[0].shadowRoot.children[1].getElementsByClassName("game-panel-max-tries")[0].textContent', msn_shopping_game_pane)):
                return True
            else:
                return False
        except:
            pass

    def isGamingCardFinishedv2() -> bool:
        """checkes if game is finished"""
        try:
            msn_shopping_game_pane = browser.execute_script('return document.querySelector("shopping-page-base")?.shadowRoot.querySelector("shopping-homepage")?.shadowRoot.querySelector("cs-feed-layout")?.shadowRoot.querySelector("msn-shopping-game-pane")')
            WebDriverWait(browser, 15).until(ec.visibility_of(msn_shopping_game_pane))
            time.sleep(2.5)
            if (browser.execute_script('return arguments[0]._dailyLimitReached', msn_shopping_game_pane)):
                return True
            else:
                return False
        except:
            pass
    
    def isGamingCardFinishedv3() -> bool:
        """checkes if game is finished"""
        try:
            msn_shopping_game_pane = browser.execute_script('return document.querySelector("shopping-page-base")?.shadowRoot.querySelector("shopping-homepage")?.shadowRoot.querySelector("cs-feed-layout")?.shadowRoot.querySelector("msn-shopping-game-pane")')
            WebDriverWait(browser, 15).until(ec.visibility_of(msn_shopping_game_pane))
            time.sleep(2.5)
            if (browser.execute_script('return arguments[0].?.shadowRoot.querySelector("msft-stripe")?.querySelector("msn-shopping-card")?.getElementsByTagName("button").length', msn_shopping_game_pane)) == 1:
                return True
            else:
                return False
        except:
            pass

    try:
        if (ARGS.headless or ARGS.virtual_display) or platform.system() == "Linux":
            browser.set_window_size(1920, 1080)
        print("[MSN GAME] Trying to complete MSN shopping game...")
        print("[MSN GAME] Checking if user is signed in ...")
        while True:
            try:
                goToURL(browser, "https://www.msn.com/en-us/shopping")
                waitUntilVisible(browser, By.TAG_NAME, 'shopping-page-base', 45)
                time.sleep(calculateSleep(15))
                try:
                    sign_in_button = getSignInButton()
                except:
                    continue
                
                if "Sign in" in sign_in_button.text:
                    signIn()
                time.sleep(calculateSleep(15))
                
                gaming_card = getGamingCard()
                if gaming_card:
                    print("[MSN GAME] Gaming card found")
                    finished = True
                    time.sleep(calculateSleep(10))
                else:
                    finished = False
                    break
                if isGamingCardFinished():
                    break
                setup_msnShoppingGame()
                time.sleep(calculateSleep(10))
                print("[MSN GAME] Answering questions ...")
                for question in range(13):
                    try:
                        print(f"[MSN GAME] Answering {question}/10", end="\r")
                        if isGamingCardFinishedv3():
                            break
                        try:
                            clickAnswer()
                        except:
                            continue
                        # closes if popup appeared
                        try:
                            browser.execute_script('if (document.querySelector("shopping-modal").shadowRoot.querySelector("#modalActionClose").shadowRoot.querySelector("button")) {document.querySelector("shopping-modal").shadowRoot.querySelector("#modalActionClose").shadowRoot.querySelector("button").click();}')
                        except:
                            pass
                        time.sleep(2)
                        if isGamingCardFinished():
                            break
                        if isGamingCardFinishedv2():
                            break
                        time.sleep(calculateSleep(15))
                    except Exception as exc:
                        displayError(exc)
                        break
                print("[MSN GAME] Refreshing Game ...")
            except:
                print("[MSN GAME] Refreshing Game ...")
                continue
    except NoSuchElementException:
        prYellow("[MSN GAME] Failed to locate MSN shopping game !")
        # finished = False
    # except GamingCardIsNotActive:
    #     prGreen("[MSN] Quiz has been already completed !")
    #     finished = True
    except Exception as exc:  # skipcq
        displayError(exc)
        prYellow("[MSN GAME] Failed to complete MSN shopping game !")
        # finished = False
    else:
        prGreen("[MSN GAME] Completed MSN shopping game successfully !")
        # finished = True
    finally:
        goToURL(browser, BASE_URL)
        LOGS[CURRENT_ACCOUNT]["MSN shopping game"] = True
        updateLogs()
        return finished

class RemainingSearches(NamedTuple):
    desktop: int
    mobile: int

    def getTotal(self) -> int:
        return self.desktop + self.mobile


def getRemainingSearches(browser: WebDriver,separateSearches: bool = False, desktopAndMobile: bool = False, isMobile: bool = False) -> RemainingSearches | int:
    """get remaining searches"""
    dashboard = getDashboardData(browser)
    searchPoints = 1
    counters = dashboard['userStatus']['counters']
    if not 'pcSearch' in counters:
        return 0, 0
    progressDesktop = counters["pcSearch"][0]["pointProgress"]
    targetDesktop = counters["pcSearch"][0]["pointProgressMax"]
    if len(counters["pcSearch"]) >= 2:
        progressDesktop = progressDesktop + counters["pcSearch"][1]["pointProgress"]
        targetDesktop = targetDesktop + counters["pcSearch"][1]["pointProgressMax"]
    if targetDesktop in [30, 90, 102]:
        # Level 1 or 2 EU/South America
        searchPoints = 3
    elif targetDesktop == 50 or targetDesktop >= 170 or targetDesktop == 150:
        # Level 1 or 2 US
        searchPoints = 5
    remainingDesktop = int((targetDesktop - progressDesktop) / searchPoints)
    remainingMobile = 0
    if dashboard["userStatus"]["levelInfo"]["activeLevel"] != "Level1":
        progressMobile = counters["mobileSearch"][0]["pointProgress"]
        targetMobile = counters["mobileSearch"][0]["pointProgressMax"]
        remainingMobile = int((targetMobile - progressMobile) / searchPoints)
    if separateSearches:
        return remainingDesktop, remainingMobile
    elif desktopAndMobile:
            return RemainingSearches(desktop=remainingDesktop, mobile=remainingMobile).getTotal()
    elif isMobile:
            return remainingMobile
    elif not isMobile:
        return remainingDesktop

def getRemainingSearchesv2(browser: WebDriver):
    """get remaining searches"""
    dashboard = getDashboardData(browser)
    searchPoints = 1
    counters = dashboard['userStatus']['counters']
    if not 'pcSearch' in counters:
        return 0, 0
    progressDesktop = counters['pcSearch'][0]['pointProgress'] + \
        counters['pcSearch'][1]['pointProgress']
    targetDesktop = counters['pcSearch'][0]['pointProgressMax'] + \
        counters['pcSearch'][1]['pointProgressMax']
    if targetDesktop == 33:
        # Level 1 EU
        searchPoints = 3
    elif targetDesktop == 55:
        # Level 1 US
        searchPoints = 5
    elif targetDesktop == 102:
        # Level 2 EU
        searchPoints = 3
    elif targetDesktop >= 170:
        # Level 2 US
        searchPoints = 5
    currentdesktopSearches = int(progressDesktop / searchPoints)
    totaldesktopSearches = int(round((targetDesktop / searchPoints)/2))
    if not currentdesktopSearches >= totaldesktopSearches:
        remainingDesktop = int(totaldesktopSearches - currentdesktopSearches)
    else:
        remainingDesktop = 0
    remainingMobile = 0
    if dashboard['userStatus']['levelInfo']['activeLevel'] != "Level1":
        progressMobile = counters['mobileSearch'][0]['pointProgress']
        targetMobile = counters['mobileSearch'][0]['pointProgressMax']
        currentmobileSearches = int(progressMobile / searchPoints)
        totalmobileSearches = int(round((targetMobile / searchPoints)/2))
        if not currentmobileSearches >= totalmobileSearches:
            remainingMobile = int(totalmobileSearches - currentmobileSearches)
        else:
            remainingMobile = 0
    return remainingDesktop, remainingMobile



def getRedeemGoal(browser: WebDriver):
    """get redeem goal"""
    user_status = getDashboardData(browser)["userStatus"]
    return user_status["redeemGoal"]["title"], user_status["redeemGoal"]["price"]


def isElementExists(browser: WebDriver, _by: By, element: str) -> bool:
    """Returns True if given element exists else False"""
    try:
        browser.find_element(_by, element)
    except NoSuchElementException:
        return False
    return True


def accountBrowser(chosen_account: str):
    """Setup browser for chosen account"""
    global CURRENT_ACCOUNT  # pylint: disable=global-statement
    for account in ACCOUNTS:
        if account["username"].lower() == chosen_account.lower():
            CURRENT_ACCOUNT = account["username"]
            break
    else:
        return None
    browser = browserSetupv3(False)
    return browser


def argumentParser():
    """getting args from command line"""

    def isValidTime(validtime: str):
        """check the time format and return the time if it is valid, otherwise return parser error"""
        try:
            t = datetime.strptime(validtime, "%H:%M").strftime("%H:%M")
        except ValueError:
            parser.error("Invalid time format, use HH:MM")
        else:
            return t

    def isSessionExist(session: str):
        """check if the session is valid and return the session if it is valid, otherwise return parser error"""
        if Path(f"{Path(__file__).parent}/Profiles/{session}").exists():
            return session
        else:
            parser.error(f"Session not found for {session}")

    parser = ArgumentParser(
        description=f"Microsoft Rewards Farmer {version}",
        allow_abbrev=False,
        usage="You may use execute the program with the default config or use arguments to configure available options."
    )
    parser.add_argument('--everyday',
                        action='store_true',
                        help='This argument will make the script run everyday at the time you start.',
                        required=False)
    parser.add_argument('--headless',
                        help='Enable headless browser.',
                        action='store_true',
                        required=False)
    parser.add_argument('--session',
                        help='Creates session for each account and use it.',
                        action='store_true',
                        required=False)
    parser.add_argument('--error',
                        help='Display errors when app fails.',
                        action='store_true',
                        required=False)
    parser.add_argument('--fast',
                        help="Reduce delays where ever it's possible to make script faster.",
                        action='store_true',
                        required=False)
    parser.add_argument('--superfast',
                        help="Reduce delays where ever it's possible even further than fast mode to make script faster.",
                        action='store_true',
                        required=False)
    parser.add_argument('--telegram',
                        help='[Optional] This argument takes token and chat id to send logs to Telegram.',
                        action='store_true',
                        required=False)
    parser.add_argument('--discord',
                        metavar='<WEBHOOK_URL>',
                        nargs=1,
                        help='This argument takes webhook url to send logs to Discord.',
                        type=str,
                        required=False)
    parser.add_argument('--edge',
                        help='Use Microsoft Edge webdriver instead of Chrome.',
                        action='store_true',
                        required=False)
    parser.add_argument('--account-browser',
                        nargs=1,
                        type=isSessionExist,
                        help='Open browser session for chosen account.',
                        required=False)
    parser.add_argument('--start-at',
                        metavar='<HH:MM>',
                        help='Start the script at the specified time in 24h format (HH:MM).',
                        nargs=1,
                        type=isValidTime)
    parser.add_argument("--on-finish",
                        help="Action to perform on finish from one of the following: shutdown, sleep, hibernate, exit",
                        choices=["shutdown", "sleep", "hibernate", "exit"],
                        required=False,
                        metavar="ACTION")
    parser.add_argument("--redeem",
                        help="Enable auto-redeem rewards based on accounts.json goals.",
                        action="store_true",
                        required=False)
    parser.add_argument("--calculator",
                        help="MS Rewards Calculator",
                        action='store_true',
                        required=False)
    parser.add_argument("--skip-unusual",
                        help="Skip unusual activity detection.",
                        action="store_true",
                        required=False)
    parser.add_argument("--skip-shopping",
                        help="Skip MSN shopping game. Useful for people living in regions which do not support MSN Shopping.",
                        action="store_true",
                        required=False)
    parser.add_argument("--no-images",
                        help="Prevent images from loading to increase performance.",
                        action="store_true",
                        required=False)
    parser.add_argument("--shuffle",
                        help="Randomize the order in which accounts are farmed.",
                        action="store_true",
                        required=False)
    parser.add_argument("--no-webdriver-manager",
                        help="Use system installed webdriver instead of webdriver-manager.",
                        action="store_true",
                        required=False)
    parser.add_argument("--currency",
                        help="Converts your points into your preferred currency.",
                        choices=["EUR", "USD", "AUD", "INR", "GBP", "CAD", "JPY",
                                 "CHF", "NZD", "ZAR", "BRL", "CNY", "HKD", "SGD", "THB"],
                        action="store",
                        required=False)
    parser.add_argument("--virtual-display",
                        help="Use PyVirtualDisplay (intended for Raspberry Pi users).",
                        action="store_true",
                        required=False)
    parser.add_argument("--dont-check-for-updates",
                        help="Prevent script from updating.",
                        action="store_true",
                        required=False)
    parser.add_argument("--repeat-shopping",
                        help="Repeat MSN shopping so it runs twice per account.",
                        action="store_true",
                        required=False)
    parser.add_argument("--skip-if-proxy-dead",
                        help="Skips the account when provided Proxy is dead/ not working",
                        action="store_true",
                        required=False)
    parser.add_argument("--dont-check-internet",
                        help="Prevent script from checking internet connection.",
                        action="store_true",
                        required=False)
    parser.add_argument("--print-to-webhook",
                        help="Print every message to webhook.",
                        action="store_true",
                        required=False)
    parser.add_argument("--recheck-proxy",
                        help="Rechecks proxy in case you face proxy dead error",
                        action="store_true",
                        required=False)
    parser.add_argument('--privacy',
                        help='[Optional] Enable privacy mode.',
                        action='store_true',
                        required=False)
    parser.add_argument('--accounts',
                        help='[Optional] Add accounts.',
                        nargs="*",
                        required=False)

    args = parser.parse_args()
    if args.superfast or args.fast:
        global SUPER_FAST, FAST  # pylint: disable=global-statement
        SUPER_FAST = args.superfast
        if args.fast and not args.superfast:
            FAST = True
        if len(sys.argv) > 1:
            for arg in vars(args):
                if "accounts" in arg or "telegram" in arg:
                    if args.privacy:
                        continue
                prBlue(f"[INFO] {arg}: {getattr(args, arg)}")
    return args


def select_and_check(remove, dct):
    dct1=copy.deepcopy(dct)
    for x in remove:
        dct1.pop(x)
    return all(dct1.values())

def logs():
    """Read logs and check whether account farmed or not"""
    global LOGS  # pylint: disable=global-statement
    shared_items = []
    try:
        # Read datas on 'logs_accounts.txt'
        LOGS = json.load(
            open(f"logs.txt", "r"))
        LOGS.pop("Elapsed time", None)
        # sync accounts and logs file for new accounts or remove accounts from logs.
        for user in ACCOUNTS:
            shared_items.append(user['username'])
            if not user['username'] in LOGS.keys():
                LOGS[user["username"]] = {"Last check": "",
                                          "Today's points": 0,
                                          "Points": 0,
                                          "Redeemable": False}
        if shared_items != LOGS.keys():
            diff = LOGS.keys() - shared_items
            for accs in list(diff):
                del LOGS[accs]

        # check that if any of accounts has farmed today or not.
        for account in LOGS.keys():
            if LOGS[account]["Last check"] == str(date.today()) and list(LOGS[account].keys()) == ['Last check',
                                                                                                   "Today's points",
                                                                                                   'Points',
                                                                                                   'Redeemable',]:
                FINISHED_ACCOUNTS.append(account)
            elif LOGS[account]['Last check'] == 'Your account has been suspended':
                FINISHED_ACCOUNTS.append(account)
            elif LOGS[account]['Last check'] == str(date.today()) and list(LOGS[account].keys()) == [
                'Last check',
                "Today's points",
                'Points',
                'Redeemable',
                'Read to Earn',
                'Daily',
                'Punch cards',
                'More promotions',
                'MSN shopping game',
                'PC searches'
            ]:
                continue
            else:
                LOGS[account]['Redeemable'] = False
                LOGS[account]['Read to Earn'] = False
                LOGS[account]['Daily'] = False
                LOGS[account]['Punch cards'] = False
                LOGS[account]['More promotions'] = False
                LOGS[account]['MSN shopping game'] = False
                LOGS[account]['PC searches'] = False
            if not isinstance(LOGS[account]["Points"], int):
                LOGS[account]["Points"] = 0
        updateLogs()
        prGreen('\n[LOGS] Logs loaded successfully.\n')
    except FileNotFoundError:
        prRed(f'\n[LOGS] "logs.txt" file not found.')
        LOGS = {}
        for account in ACCOUNTS:
            LOGS[account["username"]] = {"Last check": "",
                                         "Today's points": 0,
                                         "Points": 0,
                                         "Redeemable": False,
                                         "Read to Earn": False,
                                         "Daily": False,
                                         "Punch cards": False,
                                         "More promotions": False,
                                         "MSN shopping game": False,
                                         "PC searches": False}
        updateLogs()
        prGreen(f'[LOGS] "logs.txt" created.\n')


def updateLogs():
    """update logs"""
    _logs = copy.deepcopy(LOGS)
    for account in _logs:
        if account == "Elapsed time":
            continue
        _logs[account].pop("Redeem goal title", None)
        _logs[account].pop("Redeem goal price", None)
    with open(f'logs.txt', 'w') as file:
        file.write(json.dumps(_logs, indent=4))


def cleanLogs():
    """clean logs"""
    LOGS[CURRENT_ACCOUNT].pop("Read to Earn", None)
    LOGS[CURRENT_ACCOUNT].pop("Daily", None)
    LOGS[CURRENT_ACCOUNT].pop("Punch cards", None)
    LOGS[CURRENT_ACCOUNT].pop("More promotions", None)
    LOGS[CURRENT_ACCOUNT].pop("MSN shopping game", None)
    LOGS[CURRENT_ACCOUNT].pop("PC searches", None)


def finishedAccount():
    """terminal print when account finished"""
    New_points = POINTS_COUNTER - STARTING_POINTS
    prGreen('[POINTS] You have earned ' + str(New_points) + ' points today !')
    prGreen('[POINTS] You are now at ' + str(POINTS_COUNTER) + ' points !\n')

    FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
    if LOGS[CURRENT_ACCOUNT]["Points"] > 0 and POINTS_COUNTER >= LOGS[CURRENT_ACCOUNT]["Points"]:
        LOGS[CURRENT_ACCOUNT]["Today's points"] = POINTS_COUNTER - \
            LOGS[CURRENT_ACCOUNT]["Points"]
    else:
        LOGS[CURRENT_ACCOUNT]["Today's points"] = New_points
    LOGS[CURRENT_ACCOUNT]["Points"] = POINTS_COUNTER
    LOGS[CURRENT_ACCOUNT]["Redeemable"] = REDEEMABLE


def checkInternetConnection():
    """Check if you're connected to the inter-web superhighway"""
    if ARGS.dont_check_internet:
        return
    system = platform.system()
    while True:
        try:
            if system == "Windows":
                subprocess.check_output(
                    ["ping", "-n", "1", "8.8.8.8"], timeout=5)
            elif system == "Linux":
                subprocess.check_output(
                    ["ping", "-c", "1", "8.8.8.8"], timeout=5)
            return
        except subprocess.TimeoutExpired:
            prRed("[ERROR] No internet connection.")
            time.sleep(1)
        except FileNotFoundError:
            return
        except:
            return


def format_currency(points, currency):
    """
    Formats the given amount as a currency string.

    Args:
        amount (float): The amount to format.
        currency (str, optional): The currency code to use for formatting. Defaults to None.

    Returns:
        str: The formatted currency string.
    """
    convert = {
        "EUR": {"rate": 1500, "symbol": "€"},
        "AUD": {"rate": 1350, "symbol": "AU$"},
        "INR": {"rate": 16, "symbol": "₹"},
        "USD": {"rate": 1300, "symbol": "$"},
        "GBP": {"rate": 1700, "symbol": "£"},
        "CAD": {"rate": 1000, "symbol": "CA$"},
        "JPY": {"rate": 12, "symbol": "¥"},
        "CHF": {"rate": 1400, "symbol": "CHF"},
        "NZD": {"rate": 1200, "symbol": "NZ$"},
        "ZAR": {"rate": 90, "symbol": "R"},
        "BRL": {"rate": 250, "symbol": "R$"},
        "CNY": {"rate": 200, "symbol": "¥"},
        "HKD": {"rate": 170, "symbol": "HK$"},
        "SGD": {"rate": 950, "symbol": "S$"},
        "THB": {"rate": 40, "symbol": "฿"}
    }
    return f"{convert[currency]['symbol']}{points / convert[currency]['rate']:0.02f}"


def createMessage():
    """Create message"""
    today = date.today().strftime("%d/%m/%Y")
    BOT_NAME = os.environ.get("BOT_NAME")
    total_earned = 0
    total_overall = 0
    message = f'*{BOT_NAME}*\n\n📅 Daily report {today}\n\n'
    for index, value in enumerate(LOGS.items(), 1):
        redeem_message = None
        if value[1].get("Redeem goal title", None):
            redeem_title = value[1].get("Redeem goal title", None)
            redeem_price = value[1].get("Redeem goal price")
            redeem_count = value[1]["Points"] // redeem_price
            if ARGS.redeem:
                # only run if args.redeem mate
                if value[1]['Auto redeem']:
                    redeem_message = f"🎁 Auto redeem: {value[1]['Auto redeem']} {redeem_title} for {redeem_price} points ({redeem_count}x)\n\n"
            elif redeem_count > 1:
                redeem_message = f"🎁 Ready to redeem: {redeem_title} for {redeem_price} points ({redeem_count}x)\n\n"
            else:
                redeem_message = f"🎁 Ready to redeem: {redeem_title} for {redeem_price} points\n\n"
        if value[1]['Last check'] == str(date.today()):
            status = '✅ Farmed'
            new_points = value[1]["Today's points"]
            total_earned += new_points
            total_points = value[1]["Points"]
            is_redeemable = value[1]["Redeemable"]
            is_redeemable_text = f"✅ Redeemable" if is_redeemable else f"❌ Redeemable"
            total_overall += total_points
            message += f"{index}. {value[0]}\n📝 Status: {status}\n⭐️ Earned points: {new_points}\n🏅 Total points: {total_points}\n{is_redeemable_text}\n"
            if redeem_message:
                message += redeem_message
            else:
                message += "\n"
        elif value[1]['Last check'] == 'Your account has been suspended':
            status = '❌ Suspended'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Your account has been locked !':
            status = '⚠️ Locked'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Unusual activity detected !':
            status = '⚠️ Unusual activity detected'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Unknown error !':
            status = '⛔️ Unknown error occurred'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Your email or password was not valid !':
            status = '📛 Your email/password was invalid'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Provided Proxy is Dead, Please replace a new one and run the script again':
            status = '📛 Provided Proxy is Dead, Please replace a new one and run the script again'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        elif value[1]['Last check'] == 'Your TOTP secret was wrong !':
            status = '📛 TOTP code was wrong'
            message += f"{index}. {value[0]}\n📝 Status: {status}\n\n"
        else:
            status = f'Farmed on {value[1]["Last check"]}'
            new_points = value[1]["Today's points"]
            total_earned += new_points
            total_points = value[1]["Points"]
            total_overall += total_points
            message += f"{index}. {value[0]}\n📝 Status: {status}\n⭐️ Earned points: {new_points}\n🏅 Total points: {total_points}\n"
            if redeem_message:
                message += redeem_message
            else:
                message += "\n"
    if ARGS.currency:
        message += f"💵 Total earned points: {total_earned} "\
            f"({format_currency(total_earned, ARGS.currency)}) \n"
        message += f"💵 Total Overall points: {total_overall} "\
            f"({format_currency(total_overall, ARGS.currency)})"
    else:
        message += f"💵 Total earned points: {total_earned} "\
            f"(${total_earned / 1300:0.02f}) "\
            f"(€{total_earned / 1500:0.02f}) "\
            f"(AU${total_earned / 1350:0.02f}) "\
            f"(₹{total_earned / 16:0.02f}) \n"
        message += f"💵 Total Overall points: {total_overall} "\
            f"(${total_overall / 1300:0.02f}) "\
            f"(€{total_overall / 1500:0.02f}) "\
            f"(AU${total_overall / 1350:0.02f})"\
            f"(₹{total_overall / 16:0.02f})"

    return message


def prArgs():
    """print arguments"""
    if len(sys.argv) > 1 and not ARGS.calculator:
        total_enabled_flags = 0
        for arg in vars(ARGS):
            if getattr(ARGS, arg) is not False and getattr(ARGS, arg) is not None:
                prBlue(f"[FLAGS] {arg}: {getattr(ARGS, arg)}")
                total_enabled_flags += 1
        if total_enabled_flags == 0:
            prYellow("[FLAGS] No flags are used")


def sendReportToMessenger(message):
    """send report to messenger"""
    if ARGS.telegram:
        sendToTelegram(message)
    if ARGS.discord:
        sendToDiscord(message)


def sendToTelegram(message):
    """send to telegram"""
    t = get_notifier('telegram')
    if len(message) > 4096:
        messages = [message[i:i+4096] for i in range(0, len(message), 4096)]
        for ms in messages:
            t.notify(
                message=ms, token=os.environ.get("TOKEN", None), chat_id=os.environ.get("CHAT_ID", None), parse_mode= 'markdown')
    else:
        t.notify(message=message,
                 token=os.environ.get("TOKEN", None), chat_id=os.environ.get("CHAT_ID", None), parse_mode= 'markdown')


def sendToDiscord(message):
    """send to discord"""
    webhook_url = ARGS.discord[0]
    if len(message) > 2000:
        messages = [message[i:i + 2000] for i in range(0, len(message), 2000)]
        for ms in messages:
            content = {"username": "⭐️ Microsoft Rewards Bot ⭐️", "content": ms}
            response = requests.post(webhook_url, json=content)
    else:
        content = {"username": "⭐️ Microsoft Rewards Bot ⭐️",
                   "content": message}
        response = requests.post(webhook_url, json=content)
    if not ARGS.print_to_webhook:  # this is to prevent infinite loop
        if response.status_code == 204:
            prGreen("[LOGS] Report sent to Discord.\n")
        else:
            prRed("[ERROR] Could not send report to Discord.\n")


def setRedeemGoal(browser: WebDriver, goal: str):
    """
    Sets current account's goal for redeeming.
    @param browser - Selenium instance of the web browser.
    @param goal - Name of the goal to use.
    """
    print("[GOAL SETTER] Setting new account goal...")

    goal = goal.lower()
    goToURL(browser, "https://rewards.microsoft.com/")
    try:
        goal_name = browser.find_element(
            By.XPATH,
            value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/h3",
        )

        goal_progress = browser.find_element(
            By.XPATH,
            value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/p",
        )

        # If goal is not set or is not the specified one, then set/change it
        if "/" not in goal_progress.text.lower() or goal not in goal_name.text.lower():
            # If we need to change it, it is mandatory to refresh the set goal button
            if "/" in goal_progress.text.lower() and goal not in goal_name.text.lower():
                # Check if unspecified goal has reached 100%
                goal_progress = (
                    browser.find_element(
                        By.XPATH,
                        value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/p",
                    )
                    .text.replace(" ", "")
                    .split("/")
                )
                points = int(goal_progress[0].replace(",", ""))
                total = int(goal_progress[1].replace(",", ""))

                if points == total:
                    # Choose remove goal element instead of redeem now
                    element = browser.find_element(
                        By.XPATH,
                        value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a[2]/span/ng-transclude",
                    )
                else:
                    element = browser.find_element(
                        By.XPATH,
                        value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a/span/ng-transclude",
                    )

                element.click()
                time.sleep(3)
                element = browser.find_element(
                    By.XPATH,
                    value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a/span/ng-transclude",
                )
            else:
                element = browser.find_element(
                    By.XPATH,
                    value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a/span/ng-transclude",
                )
            element.click()
            time.sleep(3)
            elements = browser.find_elements(By.CLASS_NAME, "c-image")
            goal_found = False
            for elem in elements:
                if goal in elem.get_attribute("alt").lower():
                    elem.click()
                    goal_found = True
                    break

            if not goal_found:
                prRed(
                    "[GOAL SETTER] Specified goal not found! Search for any typos..."
                )
            else:
                prGreen("[GOAL SETTER] New account goal set successfully!")

    except (NoSuchElementException, ElementClickInterceptedException) as exc:
        prRed("[GOAL SETTER] Ran into an exception trying to redeem!")
        displayError(exc)
        return
    finally:
        goToURL(browser, BASE_URL)


def redeemGoal(browser: WebDriver):
    """
    Automatically redeems current account's goal.
    @param browser - Selenium instance of the web browser.
    """
    try:
        try:
            browser.find_element(
                By.XPATH,
                value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a[1]",
            ).click()
            time.sleep(random.uniform(5, 7))
        except (NoSuchElementException, ElementClickInterceptedException):
            browser.find_element(
                By.XPATH,
                value="/html/body/div[1]/div[2]/main/div/ui-view/mee-rewards-dashboard/main/div/mee-rewards-redeem-info-card/div/mee-card-group/div/div[1]/mee-card/div/card-content/mee-rewards-redeem-goal-card/div/div[2]/div/a[1]",
            ).click()
            time.sleep(random.uniform(5, 7))

        try:
            url = browser.current_url
            url = url.split("/")
            id = url[-1]
            try:
                browser.find_element(
                    By.XPATH, value=f'//*[@id="redeem-pdp_{id}"]'
                ).click()
                time.sleep(random.uniform(5, 7))
            except (NoSuchElementException, ElementClickInterceptedException):
                browser.find_element(
                    By.XPATH, value="/html/body/div[1]/div[2]/main/div[2]/div[2]/div[3]/a[2]"
                ).click()
            # If a cookie consent container is present, we need to accept
            # those cookies to be able to redeem the reward
            if browser.find_elements(By.ID, value="wcpConsentBannerCtrl"):
                browser.find_element(
                    By.XPATH, value="/html/body/div[3]/div/div[2]/button[1]").click()
                time.sleep(random.uniform(2, 4))
            try:
                browser.find_element(
                    By.XPATH, value='//*[@id="redeem-checkout-review-confirm"]').click()
                time.sleep(random.uniform(2, 4))
            except (NoSuchElementException, ElementClickInterceptedException):
                browser.find_element(
                    By.XPATH, value='//*[@id="redeem-checkout-review-confirm"]/span[1]').click()
        except (NoSuchElementException, ElementClickInterceptedException) as exc:
            goToURL(browser, BASE_URL)
            prRed("[REDEEM] Ran into an exception trying to redeem!")
            prRed(str(exc))
            return
        # Handle phone verification landing page
        try:
            veri = browser.find_element(
                By.XPATH, value='//*[@id="productCheckoutChallenge"]/form/div[1]').text
            if veri.lower() == "phone verification":
                prRed("[REDEEM] Phone verification required!")
                LOGS[CURRENT_ACCOUNT]['Auto redeem'] = 'Phone verification required!'
                updateLogs()
                cleanLogs()
                return
        except (NoSuchElementException, ElementClickInterceptedException):
            pass
        finally:
            time.sleep(random.uniform(2, 4))
        try:
            error = browser.find_element(
                By.XPATH, value='//*[@id="productCheckoutError"]/div/div[1]').text
            if "issue with your account or order" in error.lower():
                message = f"\n[REDEEM] {CURRENT_ACCOUNT} has encountered the following message while attempting to auto-redeem rewards:\n{error}\nUnfortunately, this likely means this account has been shadow-banned. You may test your luck and contact support or just close the account and try again on another account."
                prRed(message)
                LOGS[CURRENT_ACCOUNT]['Auto redeem'] = 'Account banned!'
                updateLogs()
                cleanLogs()
                return
        except (NoSuchElementException, ElementClickInterceptedException):
            pass
        prGreen(f"[REDEEM] {CURRENT_ACCOUNT} card redeemed!")
        LOGS[CURRENT_ACCOUNT]['Auto redeem'] = 'Redeemed!'
        updateLogs()
        cleanLogs()
        global auto_redeem_counter  # pylint: disable=global-statement
        auto_redeem_counter += 1
    except (NoSuchElementException, ElementClickInterceptedException) as exc:
        prRed("[REDEEM] Ran into an exception trying to redeem!")
        prRed(str(exc))
        return


def calculateSleep(default_sleep: int):
    """
    Sleep calculated with this formular:
    on FAST: random.uniform((default_sleep/2) * 0.5, (default_sleep/2) * 1.5)
    on SUPER_FAST: random.uniform((default_sleep/4) * 0.5, (default_sleep/4) * 1.5)
    else: default_sleep
    """
    if SUPER_FAST:
        return random.uniform((default_sleep / 4) * 0.5, (default_sleep / 4) * 1.5)
    elif FAST:
        return random.uniform((default_sleep / 2) * 0.5, (default_sleep / 2) * 1.5)
    else:
        return default_sleep


def prRed(prt):
    print(f"\033[91m{prt}\033[00m")
def prGreen(prt):
    print(f"\033[92m{prt}\033[00m")
def prYellow(prt):
    print(f"\033[93m{prt}\033[00m")
def prBlue(prt):
    print(f"\033[94m{prt}\033[00m")
def prPurple(prt):
    print(f"\033[95m{prt}\033[00m")



def tkinter_calculator():
    """Rewards Calculator GUI"""
    microsoft = 4750  # price of microsoft/xbox gift cards
    non_microsoft = 6750  # price of 3rd party gift cards

    # Create a new Tkinter window
    window = tk.Tk()
    window.title("RewardStimator - Microsoft Rewards Bot Estimator")
    window.geometry("500x280")
    window.resizable(False, False)

    # Add a title label
    title_label = ttk.Label(
        window, text="RewardStimator", font=("Helvetica", 16))
    title_label.pack(pady=10)

    # Create a frame for the form fields
    form_frame = ttk.Frame(window)
    form_frame.pack(pady=10)

    def validate_float_input(value):
        """validate input if it is float"""
        for i, _ in enumerate(value):
            if value[i] not in '0123456789.':
                return False

        # only allow 1 full stop
        if value.count(".") > 1:
            return False

        if "." in value and len(value.split(".", 1)[1]) > 2:
            return False

        return True

    def validate_numeric_input(value):
        """validate input if it is integer"""
        for i, _ in enumerate(value):
            if value[i] not in '0123456789':
                return False

        if not value == "":
            # the above if statement is required
            # otherwise it will return an error when clicking backspace
            if (int(value) > 99) or (int(value) <= 0):
                return False

        return True

    # Add a label for the price field
    price_label = ttk.Label(form_frame, text="Price:")
    price_label.grid(row=0, column=0, padx=5, pady=5, sticky="w")

    # Add an entry widget for the price field
    price_entry = ttk.Entry(form_frame, width=20, validate="key")
    price_entry.grid(row=0, column=1, padx=5, pady=5)
    price_entry.configure(validatecommand=(
        price_entry.register(validate_float_input), '%P'))

    # Add a label for the accounts field
    accounts_label = ttk.Label(form_frame, text="Accounts:")
    accounts_label.grid(row=1, column=0, padx=5, pady=5, sticky="w")

    # Add an entry widget for the accounts field
    accounts_entry = ttk.Entry(form_frame, width=20, validate="key")
    accounts_entry.grid(row=1, column=1, padx=5, pady=5)
    accounts_entry.configure(validatecommand=(
        accounts_entry.register(validate_numeric_input), '%P'))

    # Add a label for the balance field
    balance_label = ttk.Label(form_frame, text="Current Balance (default 0):")
    balance_label.grid(row=2, column=0, padx=5, pady=5, sticky="w")

    # Add an entry widget for the balance field
    balance_entry = ttk.Entry(form_frame, width=20, validate="key")
    balance_entry.grid(row=2, column=1, padx=5, pady=5)
    balance_entry.configure(validatecommand=(
        balance_entry.register(validate_float_input), '%P'))

    # Add a label for the daily points field
    daily_points_label = ttk.Label(form_frame, text="Estimated daily points:")
    daily_points_label.grid(row=3, column=0, padx=5, pady=5, sticky="w")

    # Estimated daily points
    estimated_daily_points = ttk.Entry(form_frame, width=20, validate="key")
    estimated_daily_points.grid(row=3, column=1, padx=5, pady=5)
    estimated_daily_points.configure(validatecommand=(
        estimated_daily_points.register(validate_float_input), '%P'))

    # Add a label for the associated field
    associated_label = ttk.Label(
        form_frame, text="Microsoft Associated Gift Card:")
    associated_label.grid(row=4, column=0, padx=5, pady=5, sticky="w")

    # Add radio buttons for the associated field
    associated_var = tk.BooleanVar()
    yes_radio = ttk.Radiobutton(
        form_frame, text="Yes", variable=associated_var, value=True)
    no_radio = ttk.Radiobutton(
        form_frame, text="No", variable=associated_var, value=False)
    yes_radio.grid(row=4, column=1, padx=5, pady=0, sticky="w")
    no_radio.grid(row=4, column=1, padx=5, pady=0, sticky="e")

    # Function to submit the form
    def submit():
        """run on submit button pressed"""
        price = price_entry.get()
        accounts = accounts_entry.get()
        balance = balance_entry.get()
        daily_points = estimated_daily_points.get()
        associated = associated_var.get()

        # Validate form data
        if not price or not accounts:
            messagebox.showerror("Error", "Please fill in all fields.")
            return

        try:
            price = float(price)
            accounts = int(accounts)
            balance = float(balance) if balance != "" else 0
            daily_points = float(estimated_daily_points.get())
        except ValueError:
            messagebox.showerror("Critical Error, now closing...")
            sys.exit("Error (ValueError)")

        non = '' if associated else 'Non-'
        cards_required = ceil((price - balance) / 5)
        cr_per_acc = ceil(cards_required / accounts)  # cards per account
        excess = (cr_per_acc * accounts * 5) - price + balance
        elapsed_time = ceil(
            ((microsoft if associated else non_microsoft) / daily_points) * cr_per_acc)

        if cards_required <= 0:
            messagebox.showerror(
                "Error", "Current balance is higher or equal to price.")
            return

        messagebox.showinfo("RewardStimator Result", f""
                                                     f"Total $5 {non}Microsoft gift cards required: {cards_required}"
                                                     f"\n{non}Microsoft gift cards required per account: {cr_per_acc}"
                                                     f"\nExcess: ${excess:.2f}"
                                                     f"\nEstimated elapsed elapsed_time: ~{elapsed_time} days\n")

    submit_button = ttk.Button(window, text="Submit", command=submit)
    submit_button.pack(pady=10)

    window.mainloop()


def loadAccounts():
    """get or create accounts.json"""
    global ACCOUNTS  # pylint: disable=global-statement
    ACC_ENV = os.environ.get('ACCOUNTS', None).split(' ')
    if ACC_ENV:
        ACCOUNTS = []
        for account in ACC_ENV:
            ACCOUNTS.append({"username": account.split(":")[0], "password": account.split(":")[1]})
    else:
        try:
            ACCOUNTS = json.load(open("accounts.json", "r"))
        except FileNotFoundError:
            with open("accounts.json", 'w') as f:
                f.write(json.dumps([{
                    "username": "Your Email",
                    "password": "Your Password"
                }], indent=4))
            prPurple(f"""
        [ACCOUNT] Accounts credential file "accounts.json" created.
        [ACCOUNT] Edit with your credentials and save, then press any key to continue...
            """)
            input()
            ACCOUNTS = json.load(open("accounts.json", "r"))
    if ARGS.shuffle:
        random.shuffle(ACCOUNTS)


def update_handler(local_version):
    """Checks if the update is the latest"""
    # Check if version is unknown
    if local_version == "Unknown":
        prRed("Update handler will not run due to the local version being unknown.")

    # initialize functions
    def loadingbar(configuration: dict, skip_text_after_loading_bar_finished) -> None:
        """
        eg. Loading response... [#########################]
        config = {
            "text_after_loading_bar_finished": "Successfully loaded",
            "text_before_loading_bar": "Loading response... ",
            "size_of_loading_bar": 25,
            "delay": 0.05,
            "design_of_loaded_bar": "#",
            "design_of_unloaded_bar": "."
        }
        """
        for i in range(configuration["size_of_loading_bar"]):
            sys.stdout.write(configuration["text_before_loading_bar"] + "[{0}]   \r".format(
                configuration["design_of_loaded_bar"] * (i + 1) + configuration["design_of_unloaded_bar"] * (
                    (configuration["size_of_loading_bar"] - 1) - i)))
            sys.stdout.flush()
            time.sleep(configuration["delay"])
        print(end='\x1b[2K')  # clears the line
        if not skip_text_after_loading_bar_finished:
            sys.stdout.write(configuration["text_after_loading_bar_finished"])

    def update_window(current_version, future_version, feature_list) -> None:
        """Creates tkinter window which shows available update, and it's feature list"""
        # Create the Tkinter window
        window = tk.Tk()
        window.title("New Version Available")
        window.geometry("500x400")
        window.configure(bg="#fff")
        window.resizable(False, False)
        # Add some styling
        style = ttk.Style()
        style.configure("Title.TLabel", font=(
            "Segoe UI", 16, "bold"), background="#fff", foreground="#1E90FF")
        style.configure("Feature.TLabel", font=("Segoe UI", 12),
                        background="#fff", foreground="#333")
        style.configure("Listbox.TListbox", font=(
            "Segoe UI", 12), foreground="#fff")
        # Add a label indicating a new version is available
        version_label = ttk.Label(
            window, text="A New Version is Available!", style="Title.TLabel", background="#fff")
        version_label.pack(padx=20, pady=20)
        update_label = ttk.Label(window,
                                 text=f"The current version downloaded on your device is outdated ({current_version}). A new update is available ({future_version}). To update use 'py update.py --update'.\nChange log:",
                                 style="Feature.TLabel", background="#fff", wraplength="460")
        update_label.pack(padx=20, pady=0, anchor=tk.W)
        # Add a listbox displaying features
        listbox_frame = ttk.Frame(window)
        listbox_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        listbox = tk.Listbox(listbox_frame, width=50, height=5, font=("Segoe UI", 12), background="#fff",
                             foreground="#333",
                             highlightthickness=0, bd=0, selectbackground="#1E90FF", selectforeground="#FFF",
                             relief=tk.FLAT, exportselection=False, activestyle="none", takefocus=False)
        for feature in feature_list:
            listbox.insert(tk.END, feature)
        listbox.pack(side=tk.TOP, fill=tk.BOTH, expand=True, anchor=tk.CENTER)
        # Start the Tkinter event loop
        window.mainloop()

    # function variables
    repo = r"https://raw.githubusercontent.com/farshadz1997/Microsoft-Rewards-bot/master"

    # create loading bar
    loadingbar({
        "text_after_loading_bar_finished": "",
        "text_before_loading_bar": "[UPDATER] Getting latest version from the internet...",
        "size_of_loading_bar": 25,
        "delay": 0.05,
        "design_of_loaded_bar": "#",
        "design_of_unloaded_bar": "."
    }, True)

    # GET THE LATEST VERSION - the following line if the url ends in '/'
    repo = f'{repo}version.json' if repo[-1] == "/" else f'{repo}/version.json'
    try:
        latest_version = requests.get(repo)
    except requests.exceptions.RequestException as exc:
        print("[UPDATER] Unable to check latest version. ")
        print(exc if ERROR else "")
        return

    # Error handling
    if latest_version.status_code != 200:
        print(
            f"[UPDATER] Unable to check latest version (Status: {latest_version.status_code})")
        return

    try:
        response = json.loads(latest_version.text)
    except json.JSONDecodeError:
        print("[UPDATER] Unable to check latest version (JSONDecodeError)")
        return

    # COMPARE LOCAL AND LATEST VERSION
    if local_version != response["version"]:
        if not (ARGS.headless or ARGS.virtual_display):
            update_window(
                local_version, response['version'], response['changelog'])
        prRed(f"\n[UPDATER] Your version ({local_version}) is outdated. "
              f"Please update to {response['version']} using 'py update.py --update'.")
        return
    print(f"[UPDATER] Your version ({local_version}) is up to date!")


def farmer():
    """function that runs other functions to farm."""
    global ERROR, MOBILE, CURRENT_ACCOUNT, STARTING_POINTS, REDEEMABLE, POINTS_COUNTER  # pylint: disable=global-statement
    try:
        for account in ACCOUNTS:
            CURRENT_ACCOUNT = account['username']
            if CURRENT_ACCOUNT in FINISHED_ACCOUNTS:
                continue
            if LOGS[CURRENT_ACCOUNT]["Last check"] != str(date.today()):
                LOGS[CURRENT_ACCOUNT]["Last check"] = str(date.today())
                updateLogs()
            prYellow('********************' + hide_email(CURRENT_ACCOUNT) + '********************')
            if not LOGS[CURRENT_ACCOUNT]['PC searches']:
                with browserSetupv3(False, account.get('proxy', None)) as browser :
                    print('[LOGIN]', 'Logging-in...')
                    login(browser, account['username'], account['password'], account.get(
                        'totpSecret', None))
                    prGreen('[LOGIN] Logged-in successfully !')
                    STARTING_POINTS = getBingAccountPoints(browser)
                    prGreen('[POINTS] You have ' + str(STARTING_POINTS) +
                            ' points on your account !')
                    goToURL(browser, BASE_URL)
                    waitUntilVisible(browser, By.ID, 'app-host', 30)
                    redeem_goal_title, redeem_goal_price = getRedeemGoal(browser)

                    # # Update goal if it is not the required one for auto-redeem
                    # if ARGS.redeem:
                    #     if 'goal' in account and not account['goal'].lower() in redeem_goal_title:
                    #         # Account goal does not match its json goal
                    #         goal = account["goal"].lower()
                    #     elif 'Amazon' not in redeem_goal_title:
                    #         # Account goal needs to have the default goal
                    #         print(
                    #             '[REDEEM] Goal has not been defined for this account, defaulting to Amazon gift card...'
                    #         )
                    #         goal = "amazon"
                    #     else:
                    #         # Goal is ok for this account
                    #         goal = ''
                    #     if goal != '':
                    #         # Goal needs to be updated
                    #         setRedeemGoal(browser, goal)
                    #         redeem_goal_title, redeem_goal_price = getRedeemGoal(
                    #             browser)
                    if not LOGS[CURRENT_ACCOUNT]['Read to Earn']:
                        completeReadToEarn(browser, STARTING_POINTS)
                    if not LOGS[CURRENT_ACCOUNT]['Daily']:
                        completeDailySet(browser)
                    if not LOGS[CURRENT_ACCOUNT]['Punch cards']:
                        completePunchCards(browser)
                    if not LOGS[CURRENT_ACCOUNT]['More promotions']:
                        completeMorePromotions(browser)
                    # if not ARGS.skip_shopping and not LOGS[CURRENT_ACCOUNT]['MSN shopping game']:
                    #     finished = False
                    #     if ARGS.repeat_shopping:
                    #         finished = completeMSNShoppingGame(browser, account['username'])
                    #         prYellow(
                    #             "Running repeated MSN shopping. It will likely result in error due to msn shopping likely completed")
                    #     if not finished:
                    #         finished = completeMSNShoppingGame(browser, account['username'])
                    #     REDEEMABLE = finished
                    remainingSearches, remainingSearchesM = getRemainingSearches(browser, separateSearches=True)
                    MOBILE = bool(remainingSearchesM)
                    if remainingSearches != 0:
                        print('[BING]', 'Starting Desktop and Edge Bing searches...')
                        Searches(browser, False).bingSearches()
                        POINTS_COUNTER = getBingAccountPoints(browser)
                        prGreen('\n[BING] Finished Desktop and Edge Bing searches !')
                    LOGS[CURRENT_ACCOUNT]['PC searches'] = True
                    updateLogs()
                    ERROR = False
                    browser.quit()

                    if MOBILE:
                        with browserSetupv3(True, account.get('proxy', None)) as browser:
                            print('[LOGIN]', 'Logging-in mobile...')
                            login(browser, account['username'], account['password'], account.get(
                                'totpSecret', None), True)
                            prGreen('[LOGIN] Logged-in successfully !')
                            if LOGS[account['username']]['PC searches'] and ERROR:
                                STARTING_POINTS = POINTS_COUNTER
                                goToURL(browser, BASE_URL)
                                waitUntilVisible(browser, By.ID, 'app-host', 30)
                                redeem_goal_title, redeem_goal_price = getRedeemGoal(browser)
                                remainingSearches, remainingSearchesM = getRemainingSearches(browser, separateSearches=True)
                            if remainingSearchesM != 0:
                                print('[BING]', 'Starting Mobile Bing searches...')
                                Searches(browser, True).bingSearches()
                                POINTS_COUNTER = getBingAccountPoints(browser)
                                prGreen('\n[BING] Finished Mobile Bing searches !')
                            browser.quit()
                    
                if redeem_goal_title != "" and redeem_goal_price <= POINTS_COUNTER:
                    prGreen(f"[POINTS] Account ready to redeem {redeem_goal_title} for {redeem_goal_price} points.")
                    if ARGS.redeem and auto_redeem_counter < MAX_REDEEMS:
                        # Start auto-redeem process
                        with browserSetupv3(False, account.get('proxy', None)) as browser:
                            print('[LOGIN]', 'Logging-in...')
                            login(browser, account['username'], account['password'], account.get(
                                'totpSecret', None))
                            prGreen('[LOGIN] Logged-in successfully!')
                            goToURL(browser, BASE_URL)
                            waitUntilVisible(browser, By.ID, 'app-host', 30)
                            redeemGoal(browser)
                            browser.quit()
                    if ARGS.telegram or ARGS.discord:
                        LOGS[CURRENT_ACCOUNT]["Redeem goal title"] = redeem_goal_title
                        LOGS[CURRENT_ACCOUNT]["Redeem goal price"] = redeem_goal_price
                finishedAccount()
                cleanLogs()
                updateLogs()

    except FunctionTimedOut:
        prRed('[ERROR] Time out raised.\n')
        ERROR = True
        browser.quit()
        farmer()

    except SessionNotCreatedException:
        prBlue('[Driver] Session not created.')
        prBlue(
            '[Driver] Please download correct version of webdriver form link below:')
        prBlue('[Driver] https://chromedriver.chromium.org/downloads')
        input('Press any key to close...')
        sys.exit()

    except KeyboardInterrupt:
        ERROR = True
        browser.quit()
        try:
            input(
                '\n\033[94m[INFO] Farmer paused. Press enter to continue...\033[00m\n')
            farmer()
        except KeyboardInterrupt:
            sys.exit("Force Exit (ctrl+c)")

    except ProxyIsDeadException:
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Provided Proxy is Dead, Please replace a new one and run the script again'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        prPurple(
            '\n[PROXY] Your Provided Proxy is Dead, Please replace a new one and run the script again\n')
        checkInternetConnection()
        farmer()

    except TOTPInvalidException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Your TOTP secret was wrong !'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        prRed('[ERROR] Your TOTP secret was wrong !')
        checkInternetConnection()
        farmer()

    except AccountLockedException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Your account has been locked !'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        prRed('[ERROR] Your account has been locked !')
        checkInternetConnection()
        farmer()

    except InvalidCredentialsException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Your email or password was not valid !'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        prRed('[ERROR] Your Email or password was not valid !')
        checkInternetConnection()
        farmer()

    except UnusualActivityException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Unusual activity detected !'
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        prRed("[ERROR] Unusual activity detected !")
        checkInternetConnection()
        farmer()

    except AccountSuspendedException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]['Last check'] = 'Your account has been suspended'
        LOGS[CURRENT_ACCOUNT]["Today's points"] = 'N/A'
        LOGS[CURRENT_ACCOUNT]["Points"] = 'N/A'
        cleanLogs()
        updateLogs()
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        checkInternetConnection()
        farmer()

    except RegionException:
        browser.quit()
        prRed('[ERROR] Microsoft Rewards is not available in this country or region !')
        input('[ERROR] Press any key to close...')
        os._exit(0)
    except DashboardException:
        browser.quit()
        LOGS[CURRENT_ACCOUNT]["Last check"] = "Unknown error !"
        FINISHED_ACCOUNTS.append(CURRENT_ACCOUNT)
        updateLogs()
        cleanLogs()
        checkInternetConnection()
        farmer()

    except Exception as e:
        if "executable needs to be in PATH" in str(e):
            prRed('[ERROR] WebDriver not found.\n')
            prRed(str(e))
            os._exit(0)
        displayError(e)
        print('\n')
        ERROR = True
        if browser is not None:
            browser.quit()
        checkInternetConnection()
        farmer()
    else:
        if ARGS.telegram or ARGS.discord:
            message = createMessage()
            sendReportToMessenger(message)
        FINISHED_ACCOUNTS.clear()


def main():
    """main"""
    global LANG, GEO, TZ  # pylint: disable=global-statement
    if not platform.system() == "Linux":
        # show colors in terminal
        os.system('color')
    # MS REWARD CALCULATOR
    if ARGS.calculator:
        tkinter_calculator()
        return sys.exit(0)
    prArgs()
    loadAccounts()
    downloadWebDriver()

    LANG, GEO, TZ = getCCodeLangAndOffset()
    if ARGS.account_browser:
        prBlue(f"\n[INFO] Opening session for {ARGS.account_browser[0]}")
        browser = accountBrowser(ARGS.account_browser[0])
        input("Press Enter to close when you finished...")
        if browser is not None:
            browser.close()
            browser.quit()
    # run_at = None
    # if ARGS.start_at:
    #     run_at = ARGS.start_at[0]
    # elif ARGS.everyday and ARGS.start_at is None:
    #     run_at = datetime.now().strftime("%H:%M")
    #     prBlue(f"\n[INFO] Starting everyday at {run_at}.")

    if ARGS.virtual_display:
        createDisplay()

    # if run_at is not None:
    #     prBlue(f"\n[INFO] Farmer will start at {run_at}")
    #     while True:
    #         if datetime.now().strftime("%H:%M") == run_at:
    #             if not ARGS.dont_check_for_updates:
    #                 update_handler(version)
    #             start = time.time()
    #             logs()
    #             farmer()
    #             if not ARGS.everyday:
    #                 break
    #         time.sleep(30)
    if ARGS.everyday:
        logs()
        farmer()
        while True:
            if not ARGS.dont_check_for_updates:
                update_handler(version)
            wait()
            hours = random.randint(3, 8)
            logs()
            farmer()
            time.sleep(3600 * hours)
    else:
        start = time.time()
        if not ARGS.dont_check_for_updates:
            update_handler(version)  # CHECK FOR UPDATES
        logs()
        farmer()
    end = time.time()
    delta = end - start
    hour, remain = divmod(delta, 3600)
    minutes, sec = divmod(remain, 60)
    print(f"Farmer finished in: {hour:02.0f}:{minutes:02.0f}:{sec:02.0f}")
    print(f"Farmer finished on {datetime.now().strftime('%d-%m-%Y %H:%M:%S')}")
    LOGS["Elapsed time"] = f"{hour:02.0f}:{minutes:02.0f}:{sec:02.0f}"
    updateLogs()
    if ARGS.on_finish:
        plat = platform.system()
        if ARGS.on_finish == "shutdown":
            if plat == "Windows":
                os.system("shutdown /s /t 10")
            elif plat == "Linux":
                os.system("systemctl poweroff")
        elif ARGS.on_finish == "sleep":
            if plat == "Windows":
                os.system("rundll32.exe powrprof.dll,SetSuspendState 0,1,0")
            elif plat == "Linux":
                os.system("systemctl suspend")
        elif ARGS.on_finish == "hibernate":
            if plat == "Windows":
                os.system("shutdown /h")
            elif plat == "Linux":
                os.system("systemctl hibernate")
        elif ARGS.on_finish == "exit":
            return

def kill_process_by_name(PROCNAME:str):
    for proc in psutil.process_iter(attrs=['pid', 'name']):
        if PROCNAME in proc.info['name']:
            proc.kill()

def get_version():
    """Get version from version.json"""
    try:
        VERSION_PATH = Path(__file__).parent / 'version.json'
        with open(VERSION_PATH, 'r') as version_json:
            return json.load(version_json)['version']
    except Exception as exc:  # skipcq
        displayError(exc)
        return "Unknown"


if __name__ == '__main__':
    version = get_version()
    global ARGS
    ARGS = argumentParser()
    def print(*args, **kwargs):
        if ARGS.print_to_webhook and (ARGS.telegram or ARGS.discord):
            sendReportToMessenger("```" + " ".join(args) + " ```")
        return builtins.print(*args, **kwargs)

    try:
        keep_alive()
        print("Starting...", time.sleep(random.randint(60, 120)))
        main()
    except Exception as e:
        displayError(e)